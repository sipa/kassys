#!/usr/bin/perl -w

##############################################################################
# Kas - a webapplication to manage monetary transactions among social groups #
# Copyright (C) 2006-2010  Pieter Wuille                                     #
#                                                                            #
# This program is free software: you can redistribute it and/or modify       #
# it under the terms of the GNU General Public License as published by       #
# the Free Software Foundation, version 3.                                   #
#                                                                            #
# This program is distributed in the hope that it will be useful,            #
# but WITHOUT ANY WARRANTY; without even the implied warranty of             #
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              #
# GNU General Public License for more details.                               #
#                                                                            #
# You should have received a copy of the GNU General Public License          #
# along with this program.  If not, see <http://www.gnu.org/licenses/>.      #
##############################################################################

##############################################################################
# declarations & defaults                                                    #
##############################################################################

use strict;
use DBI;
use CGI qw/:standard/;
use CGI::Carp;
use HTML::Entities;
use Encode;
use Time::Local;
use Digest;
use Data::Dumper;
use Time::HiRes 'time';

# version
my $SYSTEM="Kassys";
my $MAJOR=0;
my $MINOR=9;
my $REVISION=240;
my $VERSION="$SYSTEM v$MAJOR.$MINOR.$REVISION";
# REV=$(svn log kas.cgi | egrep '^r[0-9]+ ' | wc -l); sed -re "s/ \\\$REVISION=[0-9]+;/ \$REVISION=$REV;/" -i kas.cgi

# global constants
my $DENOM=18018000;        # 18018000 = kgv(2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,1000)
my $PCT=1.03;              # (annual) interest ratio for annuity corrections
my $SEC_PER_YEAR=31556952; # average number of seconds in gregorian year
my $THRESHOLD=0.005;       # differences below this many monetary units are ignored
my $SESSION_TIME=15;       # session lifetime, in minutes
my $UNIT="&#8364; ";       # monetary unit
my $MAX_SQL_RETRIES=10;    # how often isolated transaction can be tried

# boolean configuration parameters
my @BOOLS=('initdb','pathinfo');

# minimal authentication level for certain actions
my $MIN_LEVEL_SUDO=50;
my $MIN_LEVEL_NOPASSSUDO=90;

# database handle and prefix
my $dbh;
my $prefix="";

# authentication info
my $auth_level=0;
my $auth_uid=undef;
my $auth_fullname;
my $auth_username;
my $auth_methods="";
my $auth_active=0;
my $auth_autoaccept=0;
my $session=cookie('session');

# mails should be sent from this e-mail adres
my $mailfrom;

# cached database information
my %USERS; my $haveUSERS=0; my %FUSERS;
my %GROUPS; my $haveGROUPS=0;
my $maxExtra=undef;
my $minExtra=undef;

my ($title,$htmltitle);
my %CONF;
my @msg;

my ($URL,@path,$oldpath,$DIR,$SCRIPT);

#################################################
# global config                                 #
#################################################

$Data::Dumper::Indent=1;
$Data::Dumper::Terse=1;
$Data::Dumper::Purity=0;
$Data::Dumper::Useqq=1;
$Data::Dumper::Quotekeys=0;
$Data::Dumper::Sortkeys=1;

##############################################################################
# utility functions                                                          #
##############################################################################

sub urldecode {
  my $theURL = $_[0];
  $theURL =~ tr/+/ /;
  $theURL =~ s/%([a-fA-F0-9]{2,2})/chr(hex($1))/eg;
  $theURL =~ s/<!–(.|\n)*–>//g;
  return $theURL;
}

sub urlencode {
  my $theURL = $_[0];
  $theURL =~ s/([\W])/"%" . uc(sprintf("%2.2x",ord($1)))/eg;
  return $theURL;
}

# cut off dir part
sub filepart {
  my ($str) = @_;
  my $idx=rindex($str,'/');
  $str=substr($str,$idx+1) if ($idx>=0);
  $idx=index($str,"\000");
  $str=substr($str,0,$idx) if ($idx>=0);
  return $str;
}

# generate a url to a given path
sub genurl {
  my @p=@_;
  my $ret=$URL;
  my @q;
  my $ps;
  if (@p) {
    for my $p (@p) {
      $ps .= '/';
      $ps .= urlencode($p);
    }
    $ps=substr($ps,1);
  }
  if (defined $SCRIPT) {
    $ret .= "/$ps" if (defined $ps);
  } else {
    push @q,"/$ps" if (defined $ps);
  }
  if (@q) {
    $ret .= "?" . join('&amp;',@q);
  }
  return $ret;
}

sub pathurl {
  my @p=split(/\//,$_[0]);
  return genurl(@p);
}

sub selfurl {
  return genurl(@path);
}

# process input
sub process_input {
  my $uri=$ENV{REQUEST_URI};
  return if (!defined $uri);
  my $pos=index($uri,'?');
  $uri=substr($uri,0,$pos) if ($pos>=0);
  if (!defined $CONF{url} || $CONF{url} ne 'none') {
    $SCRIPT=filepart($ENV{SCRIPT_NAME});
  } else {
    $SCRIPT=$CONF{url};
  }
  if (defined $SCRIPT && $SCRIPT ne '') {
    $pos=index($uri,$SCRIPT);
    if ($pos>=0) {
      $pos+=length($SCRIPT);
    } elsif (substr($SCRIPT,0,1) eq '/') {
      $uri=$SCRIPT;
      $pos=length($uri);
    } else {
      $pos=length($uri);
      $SCRIPT=undef;
    }
  } else {
    $pos=length($uri);
    $SCRIPT=undef;
  }
  my $pathx=substr($uri,$pos);
  for my $arg (split(/\&/,$ENV{QUERY_STRING})) {
    $pathx=$arg if (substr($arg,0,1) eq '/');
  }
  $pathx=urldecode($pathx);
  $pathx=param('p') if (defined (param('p')));
  $pathx=url_param('p') if (defined (url_param('p')));
  @path=grep { $_ ne '' && $_ ne '.' } (split(/\//,$pathx));
  $oldpath=join('/',@path);
  $URL=substr($uri,0,$pos);
  $pos=rindex($URL,'/');
  $DIR = ($pos>=0 ? substr($URL,0,$pos) : "/");
}


# generation of (pseudo)random session id's
my $SIDCHAR='abcdefghijklmopqrstuvwxyzABCDEFGHIJKLMOPQRSTUVWXYZ0123456789';
my $SIDPOS=length($SIDCHAR);
my $SIDGEN=16777216;

sub generate_sid {
  my ($bits) = @_;
  my $sidlen=int($bits*log(2)/log($SIDPOS)+1);
  my $r="";
  my $n=0;
  my $x=1;
  while (length($r)<$sidlen) {
    if ($x<$SIDPOS*$SIDPOS) {
      $n = $n*$SIDGEN + int(rand($SIDGEN));
      $x = $x*$SIDGEN;
    }
    $r .= substr($SIDCHAR,$n % $SIDPOS,1);
    $x = int($x/$SIDPOS);
    $n = int($n/$SIDPOS);
  }
  return $r;
}

# maximum of a list
sub max {
  my $val=pop @_;
  foreach (@_) {
    $val=$_ if ($_ > $val);
  }
  return $val;
}

# minimum of a list
sub min {
  my $val=pop @_;
  foreach (@_) {
    $val=$_ if ($_ < $val);
  }
  return $val;
}

# log something
sub log_action {
  open LOG,">>kas.log" || die "Cannot open log";
  foreach (@_) {
    chomp;
    print LOG "[".time.(defined $auth_uid ? " #$auth_uid" : "")."] $_\n";
  }
  close LOG;
}

# number E
sub e {
  return 2.718281828459045235;
 }

# allowed functions + function evaluator
my %FUNCS=(abs => 1, exp => 1, log => 1, int => 1, rand => 1, sqrt => 1);
sub calc {
  my ($x)=@_;
  return undef if (!defined $x);
  $x = lc($x);
  $x =~ s/\[.*?\]//g; # remove comments
  $x =~ s/\,/\./g;    # replace , by .
  $x =~ s/\s+//g;     # remove spaces
  return 0 if ($x eq '');
  return undef if ($x =~ /[^a-z0-9.+*\/()\t-]/);  # exit if non-alphanumeric characters other than .+-*/() are used
  foreach (split(/[^a-z]+/,$x)) {  # check all alphabetical strings
    return undef if (!defined $FUNCS{$_});
  }
  return eval($x);
}

# greatest common divisor
sub gcd {
  my ($a,$b)=@_;
  do {
    if ($a>$b) { my $c=$a; $a=$b; $b=$c; }
    return $b if ($a==0);
    $b %= $a;
  } while(1);
}

sub gen_key {
  my ($pass,$algo) = @_;
  $algo='MD5' if (!defined $algo);
  my $salt=generate_sid(32);
  my $ctx=Digest->new($algo);
  $ctx->add("$salt $pass $salt");
  return $algo.' '.$salt.' '.($ctx->b64digest);
}

sub test_key {
  my ($pass,$key) = @_;
  my ($algo,$salt,$digest) = split(/ /,$key);
  my $ctx=Digest->new($algo);
  $ctx->add("$salt $pass $salt");
  return ($digest eq ($ctx->b64digest));
}

sub normalize_name {
  my ($name) = @_;
  $name =~ s/\A\s*(.*?)\s*\Z/$1/;
  $name =~ s/\s+/ /g;
  return $name;
}

sub parsedate {
  my ($str) = @_;
  if ($str =~ /(\d+)-(\d+)-(\d+) (\d+):(\d+):([0-9.]+)/) {
    return timelocal(0,$5,$4,$3,$2-1,$1-1900)+$6;
  } else {
    return time;
  }
}

#####################################################
# IBAN VERIFICATION                                 #
#####################################################

# retrieved from http://www.swift.com/solutions/messaging/information_products/bic_downloads_documents/pdfs/IBAN_Registry.pdf
# Release 18, May 2010
my %BBAN=(
  AL => "8!n16!c",       AD => "4!n4!n12!c",          AT => "5!n11!n",
  BE => "3!n7!n2!n",     BA => "3!n3!n8!n2!n",        BG => "4!a4!n2!n8!c",
  HR => "7!n10!n",       CY => "3!n5!n16!c",          CZ => "4!n6!n10!n",
  DK => "4!n9!n1!n",     FO => "4!n9!n1!n",           GL => "4!n9!n1!n",
  EE => "2!n2!n11!n1!n", FI => "6!n7!n1!n",           FR => "5!n5!n11!c2!n",
  DE => "8!n10!n",       GE => "2!a16!n",             GI => "4!a15!c",
  GR => "3!n4!n16!c",    HU => "3!n4!n1!n15!n1!n",    IS => "4!n2!n6!n10!n",
  IE => "4!a6!n8!n",     IL => "3!n3!n13!n",          IT => "1!a5!n5!n12!c",
  LV => "2!n4!a13!c",    LB => "4!n20!c",             LI => "5!n12!c",
  LT => "5!n11!n",       LU => "3!n13!c",             MK => "3!n10!c2!n",
  MT => "4!a5!n18!c",    MU => "4!a2!n2!n12!n3!n3!a", MC => "5!n5!n11!c2!n",
  ME => "3!n13!n2!n",    NL => "4!a10!n",             NO => "4!n6!n1!n",
  PL => "8!n16n",        PT => "4!n4!n11!n2!n",       RO => "4!a16!c",
  SM => "1!a5!n5!n12!c", SA => "2!n18!c",             RS => "3!n13!n2!n",
  SK => "4!n6!n10!n",    SI => "5!n8!n2!n",           ES => "4!n4!n1!n1!n10!n",
  SE => "3!n16!n1!n",    CH => "5!n12!c",             TN => "2!n3!n13!n2!n",
  TR => "5!n1!c16!c",    UK => "4!a6!n8!n"
);

sub iban_to_re {
  my ($ibe) = @_;
  my $re="";
  while ($ibe =~ /\A(\d*)(!?)([a-z])(.*)\Z/) {
    my $num=$1 || 1;
    my $strict=($2 eq '!');
    my $type=$3;
    $ibe=$4;
    if ($type eq 'a') {
      $re .= '[A-Z]';
    } elsif ($type eq 'n') {
      $re .= '[0-9]';
    } elsif ($type eq 'c') {
      $re .= '[A-Z0-9]';
    } elsif ($type eq 'e') {
      $re .= ' ';
    } else {
      $re .= '.';
    }
    if ($strict) {
      $re .= "{$num}";
    } else {
      $re .= "{1,$num}";
    }
  }
  return $re;
}
sub lmod {
  my ($num,$mod)=@_;
  my $sum=0;
  my $mult=1;
  for my $i (1..length($num)) {
    my $n=substr($num,length($num)-$i,1);
    $sum = ($sum+$n*$mult) % $mod;
    $mult = (10*$mult) % $mod;
  }
  return $sum;
}
sub eleventest {
  my ($num)=@_;
  my $sum=0;
  my $mult=1;
  for my $i (1..length($num)) {
    my $n=substr($num,length($num)-$i,1);
    $sum = ($sum+$n*$mult) % 11;
    $mult = ($mult+1) % 11;
  }
  return $sum;
}

sub parse_bban {
  my ($cc,$bban) = @_;
  if ($cc eq 'BE') {
    my $val=substr($bban,0,10);
    my $mod=lmod($val,97) || 97;
    return $bban if (substr($bban,10,2) eq $mod);
    return undef;
  } elsif ($cc eq 'NL') {
    my $val=substr($bban,4);
    my $mod=eleventest($val);
    return $bban if ($mod==0);
    return undef;
  }
  return $bban;
}

sub parse_iban {
  my ($an) = @_;
  my $iban=$an;
  $iban =~ s/[^0-9a-zA-Z?]//g;
  $iban = uc($iban);
  if ($iban =~ /\A([A-Z]{2})(\?\?|[0-9]{2})(.*)\Z/) { # looks like IBAN
    my $cc=$1;
    my $crc=$2;
    my $bban=$3;
    if (defined $BBAN{$cc}) {
      my $re=iban_to_re($BBAN{$cc});
      return undef if ($bban !~ /\A$re\Z/); # doesn't match national structure
      my $mb=$bban.$cc.'00';
      $mb =~ s/([A-Z])/sprintf("%02i",ord($1)-55)/eg;
      my $mod=lmod($mb,97);
      my $ccrc=sprintf("%02i",98-$mod);
      return undef if ($crc ne '??' && $crc ne $ccrc); # check digits are invalid
      $bban=parse_bban($cc,$bban);
      return undef if (!defined $bban); # national test fails
      $iban=$cc.$ccrc.$bban;
      $iban =~ s/([a-zA-Z0-9]{4})\B/$1 /g;
      return $iban;
    }
  }
  my $res; 
  $res=parse_iban('BE??'.$iban) if ($an =~ /\A[0-9]{12}\Z/ || $an =~ /\A\d{3}-\d{7}-\d{2}\Z/); return $res if (defined $res);
  return undef;
}

##############################################################################
# database functions                                                         #
##############################################################################

# establish database connection
sub db_connect {
  my $dbname=$CONF{dbname};
  my $host=$CONF{dbhost} || "localhost";
  my $dbusername=$CONF{dbuser};
  my $dbpassword=$CONF{dbpass};
  $dbh = DBI->connect("dbi:Pg:dbname=$dbname;host=$host", $dbusername, $dbpassword,{AutoCommit => 1,RaiseError => 0});
  $prefix=defined($CONF{dbprefix}) ? "$CONF{dbprefix}_" : "";
  $title=$CONF{title} || $VERSION;
  $htmltitle=$CONF{htmltitle} || $title;
  $mailfrom=$CONF{mailfrom};
  $dbh->do("SET SESSION CHARACTERISTICS AS TRANSACTION ISOLATION LEVEL SERIALIZABLE");
}

my $DB_ISOLATED=0;

# run a closure in database isolation
# possible results:
# (0,@ret)          - success
# (1,$@)            - user error
# (2,$state,$error) - db error
# (3)               - aborted (empty @ret)
sub db_isolate {
  my ($f,@args) = @_;
  # set local config
  local $dbh->{AutoCommit} = 0;
  local $dbh->{RaiseError} = 1;
  local $dbh->{PrintError} = 0;
  # counter for retries
  my $num=0;
  # result of transaction
  my @ret;
  # succesfull?
  my $succ;
  # loop until either failure, success, or retry limit exceeded
  while (1) {
    # try the magic
    $DB_ISOLATED=1;
    eval {
      @ret=$f->(@args);
      if ($#ret>=0) {
        $dbh->commit;
        $succ=0;
      } else {
        $succ=3;
      }
    };
    my $usererr=$@;
    my $dberr=$dbh->state;
    my $pgerr=$dbh->err;
    my $dberrstr=$dbh->errstr;
    $DB_ISOLATED=0;
    # handle abort
    if (defined($succ) && $succ==3) {
      eval { $dbh->rollback; };
      last;
    }
    # no abort, just failure
    if ($usererr) {
      # try to clean up
      eval { $dbh->rollback; };
      # check whether it's a transaction that needs a retry
      if ($pgerr == 6) {
        $num++;
        if ($num==$MAX_SQL_RETRIES) {
          print STDERR "Too many retries, giving up: [$pgerr/$dberr: $dberrstr]\n";
          $succ=2; @ret=($pgerr,$dberrstr);
        } else {
          print STDERR "Concurrency failure: [$pgerr/$dberr] retry $num\n";
          next; # retry
        }
      } else {
        if ($pgerr>2) {
          print STDERR "Database error: [$pgerr/$dberr: $dberrstr]\n";
          $succ=2; @ret=($pgerr,$dberrstr);
        } else {
          print STDERR "Non-database error in transaction: $usererr\n";
          $succ=1; @ret=($usererr);
        }
      }
    }
    # if we didn't call next for a retry, we succeeded or failed; break out of loop
    last;
  }
  # return result or undef
  return ($succ,@ret);
}

sub db_isolated {
  if (!$DB_ISOLATED) {
    die "Database transaction running without isolation!";
  }
}

sub db_prepare {
  my ($stm) = @_;
  $stm =~ s/#/$prefix/g;
  return $dbh->prepare($stm);
}

sub db_do {
  my ($stm) = @_;
  $stm =~ s/#/$prefix/g;
  return $dbh->do($stm);
}

# TODO: incorporate following changes:
# - descriptions in items
# - comments on effects
# - accnr -> (iban,bic)
sub db_reset {
  die "Resetting database requires 'initdb true' in kas.conf" unless ($CONF{initdb});
  
  {
    local $dbh->{Warn} = 0;
    local $dbh->{RaiseError} = 0;
    local $dbh->{PrintError} = 0;
    local $dbh->{AutoCommit} = 1;

    db_do("DROP INDEX #IDX_MSG_SID_TS CASCADE");
    db_do("DROP INDEX #IDX_SESSION_EXPIRE CASCADE");
    db_do("DROP INDEX #IDX_USERREQ_EXPIRE CASCADE");
    db_do("DROP INDEX #IDX_SHARES_GID CASCADE");
    db_do("DROP INDEX #IDX_TR_WWHEN CASCADE");
    db_do("DROP INDEX #IDX_TR_AFG CASCADE");
    db_do("DROP INDEX #IDX_EF_TID CASCADE");
    db_do("DROP INDEX #IDX_EF_UID CASCADE");
    db_do("DROP INDEX #IDX_VISIBLE_SEER CASCADE");
    db_do("DROP INDEX #IDX_EDGEINFO_ETYP_EFROM CASCADE");
    db_do("DROP INDEX #IDX_EDGEINFO_ETYP_ETO CASCADE");
  
    db_do("DROP VIEW #USERLIST CASCADE");

    db_do("DROP TABLE #MSG CASCADE");
    db_do("DROP TABLE #SESSION CASCADE");
    db_do("DROP TABLE #VISIBLE CASCADE");
    db_do("DROP TABLE #EDGEINFO CASCADE");
    db_do("DROP TABLE #BILL CASCADE");
    db_do("DROP TABLE #ITEM CASCADE");
    db_do("DROP TABLE #EF CASCADE");
    db_do("DROP TABLE #TR CASCADE");
    db_do("DROP TABLE #SHARES CASCADE");
    db_do("DROP TABLE #GROUPS CASCADE");
    db_do("DROP TABLE #HTAUTH CASCADE");
    db_do("DROP TABLE #PWAUTH CASCADE");
    db_do("DROP TABLE #USERREQ CASCADE");
    db_do("DROP TABLE #USERS CASCADE");

    db_do("DROP SEQUENCE #NTR CASCADE");
    db_do("DROP SEQUENCE #NGROUPS CASCADE");
    db_do("DROP SEQUENCE #NUSERS CASCADE");
  }

  db_do("CREATE SEQUENCE #NUSERS");
  db_do("CREATE SEQUENCE #NGROUPS");
  db_do("CREATE SEQUENCE #NTR");

  db_do("CREATE TABLE #USERS (".   # list of active users
          "UID INT4 PRIMARY KEY NOT NULL DEFAULT nextval('#NUSERS'), ".  # unique user id
          "UNAME VARCHAR(63) NOT NULL, ".  # unique username
          "FULLNAME TEXT NOT NULL, ".      # full name
          "IBAN VARCHAR(40), ".            # international bank account number
          "BIC VARCHAR(12), ".             # bank identifier code
          "ACTIVE BOOLEAN NOT NULL DEFAULT FALSE, ". # active user?
          "EMAIL VARCHAR(255) NOT NULL, ". # email address
          "TOTALSUM NUMERIC(20,10) NOT NULL DEFAULT 0, ".  # sum of all included (counted) transactions for this user
          "TOTALPCT NUMERIC(20,10) NOT NULL DEFAULT 0, ".  # same, but annuity-corrected for the timestamp represented by 'created' field
          "CREATED TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP, ". # when account was created (not requested)
          "I18N VARCHAR(3) NOT NULL DEFAULT 'en', ". # language
          "AUTOACCEPT NUMERIC(12,4) NULL DEFAULT NULL, ". # automatically accept charges up to this amount (NULL=everything)
          "NICKNAME VARCHAR(40) NULL DEFAULT NULL, ". # nickname
          "UNIQUE (UNAME), ".
          "UNIQUE (EMAIL)".
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #USERREQ (". # list of user-account requests
          "RID VARCHAR(63) PRIMARY KEY NOT NULL, ". # unique request ID
          "EXPIRE TIMESTAMP NOT NULL DEFAULT (CURRENT_TIMESTAMP + interval '7 days'), ". # when does request expire
          "UNAME VARCHAR(63) NULL, ".      # requested username
          "UID INT4 NULL REFERENCES #USERS, ". # user to edit (when changing password)
          "FULLNAME TEXT NULL, ".          # provided fullname
          "ACCNR VARCHAR(40), ".           # provided account number (IBAN)
          "EMAIL VARCHAR(255) NULL, ".     # provided email adres
          "HTNAME VARCHAR(64) NULL, ".     # http-auth username during account request
          "PWKEY VARCHAR(255) NULL, ".     # requested password (encoded using gen_key)
          "LEVEL INT4 NOT NULL DEFAULT 1". # requested permission level (TODO: check this when creating account...)
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #PWAUTH (".  # password-based authentication list
          "UID INT4 NOT NULL REFERENCES #USERS, ". # user-id this password is valid for
          "KEY VARCHAR(255) NOT NULL, ".   # password stored as a key (using gen_key)
          "LEVEL INT4 NOT NULL DEFAULT 1, ". # permission level
          "UNIQUE (UID)".
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #HTAUTH (".  # http-auth based authentication list
          "UID INT4 NOT NULL REFERENCES #USERS, ". # user-id this http-auth is valid for
          "HTNAME VARCHAR(64) PRIMARY KEY NOT NULL, ". # what name to use
          "LEVEL INT4 NOT NULL DEFAULT 1, ". # permission level
          "UNIQUE (UID)".
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #GROUPS (".
          "GID INT4 PRIMARY KEY NOT NULL DEFAULT nextval('#NGROUPS'), ". # unique group identifier
          "DEFINER INT4 NOT NULL REFERENCES #USERS, ". # who created the group
          "NAME VARCHAR(40) NOT NULL, ". # name of the group
          "DESCR TEXT NULL, ". # description of the group
          "ISPUBLIC BOOL NOT NULL DEFAULT FALSE, ". # whether group is public
          "MAX INT4 NOT NULL DEFAULT 0, ".          # maximum number of shares (if larger than total: unassigned)
          "MAXFORM TEXT, ".        # formula for maximum number of shares
          "WWHEN TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP, ". # creation time
          "UNIQUE (NAME,WWHEN)".
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #SHARES (".
          "GID INT4 REFERENCES #GROUPS NOT NULL, ". # group this is a share of
          "UID INT4 REFERENCES #USERS NOT NULL, ".  # user that is share of group
          "AMOUNT INT4 NOT NULL CHECK (amount>0), ".        # how many shares
          "FORMULA TEXT, ". # formula for shares
          "UNIQUE (GID,UID)".
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #TR (". # transactions (payments, items, bills, ...)
          "TID INT8 PRIMARY KEY NOT NULL DEFAULT nextval('#NTR'), ". # transaction id
          "TYP CHAR NOT NULL, ". # what type ('i'=item/payment, 'b'=bill)
          "NAME VARCHAR(40) NULL, ". # name of item/bill (nameless item against a user = payment)
          "DESCR TEXT NULL, ". # extra description (currently unused in payments)
          "AUTHOR INT4 NOT NULL REFERENCES #USERS, ". # who created the transaction
          "WWHEN TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP, ". # creation time of transaction
          "AFG INT4 NULL REFERENCES #GROUPS, ". # affected user
          "AFU INT4 NULL REFERENCES #USERS,".    # affected group
          "COUNTED BOOL NOT NULL DEFAULT FALSE". # whether transaction is counted
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #EF (". # effect of a transaction
          "TID INT8 NOT NULL REFERENCES #TR, ". # transaction this is an effect of
          "UID INT4 NOT NULL REFERENCES #USERS, ". # user that is affected
          "AMOUNT NUMERIC(18,10) NOT NULL DEFAULT 0, ". # for which amount
          "SEEN NUMERIC(18,10) NOT NULL DEFAULT 0, ".   # which amount was (either positively or negatively) acknowledged by user
          "ACCEPT BOOL NOT NULL DEFAULT TRUE, ". # true=accepted, false=declined
          "ENABLED BOOL NOT NULL DEFAULT FALSE, ". # whether this effect is/should be counted in totals
          "COMMENT TEXT NULL, ". # comments - currently unused
          "PRIMARY KEY (TID,UID) ".
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #ITEM (". # simple type of transactions (require #TR.TYP='i')
          "TID INT8 NOT NULL REFERENCES #TR, ".  # transaction id
          "AMOUNT NUMERIC(12,4), ".              # price/payment
          "UNIQUE (TID) ".
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #BILL (".# more advanced type of transactions (require #TR.TYP='b')
          "TID INT8 NOT NULL REFERENCES #TR, ".  # transaction id
          "DEFINITION TEXT NOT NULL, ".          # definition
          "UNIQUE (TID) ".
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #EDGEINFO (". # information about edges 
          "EFROM INT4 REFERENCES #USERS NOT NULL, ". # information about edge from this author
          "ETO INT4 REFERENCES #USERS NOT NULL, ".   # to this affected user
          "ETYP CHAR NOT NULL, ".                    # of this type (currently only 'd' - direct)
          "TOTALSUM NUMERIC(20,10) NOT NULL DEFAULT 0, ".
          "TOTALPCT NUMERIC(20,10) NOT NULL DEFAULT 0, ".
          "CREATED TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP, ".
          "PRIMARY KEY (ETYP,EFROM,ETO)".
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #VISIBLE (".
          "SEER INT4 REFERENCES #USERS NOT NULL, ".
          "SEEN INT4 REFERENCES #USERS NOT NULL, ".
          "LEVEL DOUBLE PRECISION NOT NULL DEFAULT 1, ".
          "PRIMARY KEY (SEER,SEEN) ".
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #SESSION (".
          "SID VARCHAR(86) PRIMARY KEY NOT NULL, ".
          "UID INT4 REFERENCES #USERS NOT NULL, ".
          "EXPIRE TIMESTAMP NOT NULL, ".
          "LEVEL INT4 NOT NULL ".
        ") WITHOUT OIDS");
  db_do("CREATE TABLE #MSG (".
          "SID VARCHAR(86) NOT NULL, ".
          "MTYP VARCHAR(8) NOT NULL, ".
          "MSG TEXT NOT NULL, ".
          "TS TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP".
        ") WITHOUT OIDS");
  db_do(
    "CREATE VIEW #USERLIST AS ".
      "SELECT U.UID AS UID, U.ACTIVE, U.FULLNAME AS NAME, U.TOTALSUM as TOTAL, U.TOTALPCT*POW($PCT,EXTRACT(EPOCH FROM (CURRENT_TIMESTAMP-U.CREATED))/$SEC_PER_YEAR)-U.TOTALSUM AS EXTRA, U.ACCNR AS ACCNR ".
        "FROM #USERS AS U"
  );

  db_do("CREATE INDEX #IDX_SHARES_GID          ON #SHARES   (GID)");
  db_do("CREATE INDEX #IDX_TR_WWHEN            ON #TR       (WWHEN)");
  db_do("CREATE INDEX #IDX_TR_AFG              ON #TR       (AFG)");
  db_do("CREATE INDEX #IDX_EF_TID              ON #EF       (TID)");
  db_do("CREATE INDEX #IDX_EF_UID              ON #EF       (UID)");
  db_do("CREATE INDEX #IDX_VISIBLE_SEER        ON #VISIBLE  (SEER)");
  db_do("CREATE INDEX #IDX_EDGEINFO_ETYP_EFROM ON #EDGEINFO (ETYP,EFROM)");
  db_do("CREATE INDEX #IDX_EDGEINFO_ETYP_ETO   ON #EDGEINFO (ETYP,ETO)");
  db_do("CREATE INDEX #IDX_SESSION_EXPIRE      ON #SESSION  (EXPIRE)");
  db_do("CREATE INDEX #IDX_USERREQ_EXPIRE      ON #USERREQ  (EXPIRE)");
  db_do("CREATE INDEX #IDX_MSG_SID_TS          ON #MSG      (SID,TS)");
}

# initialize database
sub db_init {
  require Term::ReadKey;
  import Term::ReadKey;
  $|=1;
  print "(Re)initializing the database. Cancel now if you do not want to do this.\nAdmin password: ";
  ReadMode('noecho');
  my $pass1=<STDIN>; chomp $pass1;
  ReadMode('normal');
  print "\nRepeat: ";
  ReadMode('noecho');
  my $pass2=<STDIN>; chomp $pass2;
  ReadMode('normal');
  print "\n";
  die "Passwords do not match" if ($pass1 ne $pass2);
  die "Password too short" if (length($pass1)<6);
  print "Admin e-mail: ";
  my $email=<STDIN>; chomp $email;
  db_reset;
  print STDERR "Start creating entries...\n";
  my $sth=db_prepare("INSERT INTO #USERS (uid,uname,fullname,email) VALUES (-1,'admin','Administrator',?)");
  $sth->execute($email);
  db_do("INSERT INTO #PWAUTH (uid,key,level) VALUES (-1,'".gen_key($pass1)."',100)");
  print STDERR "done initialising...\n";
  print "Now remove the 'initdb' setting from kas.conf, and log in using the webinterface as 'admin'.\n";
}

sub check_auth {
  my ($usern) = @_;
  my $password=param('password');
  my $username=$usern || param('username');
  $auth_level=-1;
  $auth_methods="";
  # use session-based auth
  if (defined $session) {
    my $sth2=db_prepare("DELETE FROM #SESSION WHERE EXPIRE<CURRENT_TIMESTAMP");
    $sth2->execute;
    my $sth=db_prepare("SELECT S.UID,S.LEVEL,U.FULLNAME,U.UNAME,U.ACTIVE,U.AUTOACCEPT FROM #SESSION AS S, #USERS AS U WHERE S.SID=? AND S.UID=U.UID");
    $sth->execute($session);
    my ($uid,$level,$name,$uname,$active,$autoaccept) = $sth->fetchrow_array;
    if (defined $uid) { # not expired, and matching session
      $auth_uid=$uid;
      $auth_level=max($auth_level,$level);
      $auth_fullname=$name;
      $auth_active=$active;
      $auth_username=$uname;
      $auth_autoaccept=$autoaccept;
      $auth_methods .= "|session|";
      my $sth3=db_prepare("SELECT M.MTYP,M.MSG FROM #MSG M WHERE M.SID=? ORDER BY M.TS");
      $sth3->execute($session);
      while (my ($mtyp,$msg) = $sth3->fetchrow_array) {
        push @msg,[$mtyp,$msg];
      }
      $sth3=db_prepare("DELETE FROM #MSG WHERE SID=?");
      $sth3->execute($session);
    } else {
      undef $session; # no valid $session - clear it to recreate it later
    }
  }
  # try http auth
  if ($auth_level<0 && defined $ENV{REMOTE_USER}) {
    my $sth4=db_prepare("SELECT A.UID,A.LEVEL,U.FULLNAME,U.UNAME,U.ACTIVE,U.AUTOACCEPT FROM #HTAUTH AS A, #USERS AS U WHERE A.HTNAME=? AND U.UID=A.UID");
    $sth4->execute($ENV{REMOTE_USER});
    my ($uid,$level,$name,$uname,$active,$autoaccept)=$sth4->fetchrow_array;
    if (defined($uid)) {
      $auth_uid=$uid;
      $auth_level=max($auth_level,$level);
      $auth_fullname=$name;
      $auth_username=$uname;
      $auth_active=$active;
      $auth_autoaccept=$autoaccept;
      $auth_methods .= "|http|";
      $sth4->finish;
    }
    $sth4->finish;
  }
  # try password auth
  if (defined $username && $username ne '' && ($auth_level>=$MIN_LEVEL_NOPASSSUDO || defined $password)) {
    my $sth3=db_prepare("SELECT A.UID,A.KEY,A.LEVEL,U.FULLNAME,U.UNAME,U.ACTIVE,U.AUTOACCEPT FROM #PWAUTH AS A, #USERS AS U WHERE U.UNAME=? AND U.UID=A.UID");
    $sth3->execute($username);
    my $cnt=0;
    while (my ($uid,$key,$level,$name,$uname,$active,$autoaccept)=$sth3->fetchrow_array) {
      $cnt++;
      if (($auth_level>=$MIN_LEVEL_NOPASSSUDO && $level<$auth_level) || (test_key($password,$key))) {
        if ($auth_level>=$MIN_LEVEL_SUDO) { # without sudo rights, drop to level of new user, otherwise keep level
          $auth_level=max($auth_level,$level);
        } else {
          $auth_level=$level;
        }
        $auth_uid=$uid;
        $auth_fullname=$name;
        $auth_username=$uname;
        $auth_active=$active;
        $auth_autoaccept=$autoaccept;
        $auth_methods .= "|password|";
        $sth3->finish;
        @path=() if (defined $path[0] && $path[0] eq 'login');
        last;
      } else {
        push @msg,['warn',"Password mismatch"] if (!defined $auth_username);
      }
    }
    push @msg,['warn',"User not found"] if ($cnt==0 && !defined $auth_username);
    $sth3->finish;
  }
  # update session cache
  if ($auth_level>0) {
    my $sth5;
    if (!defined $session) { # no valid session already in session table - create new one
      $session=generate_sid(256);
      $sth5=db_prepare("INSERT INTO #SESSION (UID,LEVEL,SID,EXPIRE) VALUES (?,?,?,CURRENT_TIMESTAMP + INTERVAL '${SESSION_TIME} minutes')");
    } else { # update old session entry
      $sth5=db_prepare("UPDATE #SESSION SET UID=?, LEVEL=?, EXPIRE=CURRENT_TIMESTAMP + INTERVAL '${SESSION_TIME} minutes' WHERE SID=?");
    }
    $sth5->execute($auth_uid,$auth_level,$session);
  }
}

# fetch & cache user list
sub need_user_list {
  return if (!defined $auth_username);
  my ($full)=@_;
  if (defined $full) {
    my $sth=db_prepare("SELECT UID,FULLNAME,ACTIVE FROM #USERS");
    $sth->execute;
    while (my ($uid,$name,$active)=$sth->fetchrow_array) {
      $USERS{$uid}->{NAME}=$name;
      $USERS{$uid}->{UID}=$uid;
      $USERS{$uid}->{ACTIVE}=$active;
    }
    $haveUSERS=0;
  }
  if (!$haveUSERS) {
    $haveUSERS=1;
    my $sth=db_prepare("SELECT UID,NAME,TOTAL,EXTRA,ACCNR,ACTIVE FROM #USERLIST WHERE UID=? OR (UID IN (SELECT SEEN FROM #VISIBLE WHERE SEER=? UNION SELECT ETO FROM #EDGEINFO WHERE EFROM=? AND (TOTALSUM!=0 OR TOTALPCT!=0) AND ETYP='d')) ORDER BY NAME");
    $sth->execute($auth_uid,$auth_uid,$auth_uid);
    while (my ($uid,$name,$total,$extra,$accnr,$active) = $sth->fetchrow_array) {
      $USERS{$uid}={UID => $uid, NAME => $name, TOTAL => $total, EXTRA => $extra, ACCNR => $accnr, ACTIVE => $active};
      $minExtra=$extra if (!defined($minExtra) || (defined($minExtra) && $extra<$minExtra));
      $maxExtra=$extra if (!defined($maxExtra) || (defined($maxExtra) && $extra>$maxExtra));
      $USERS{$uid}->{ORD} = $total;
      my $fname=normalize_name($name);
      $FUSERS{lc($fname)}=$uid;
    }
    $sth->finish;
    $sth=db_prepare("SELECT SEEN,LEVEL FROM #VISIBLE WHERE SEER=? AND SEEN!=SEER");
    $sth->execute($auth_uid);
    while (my ($uid,$level) = $sth->fetchrow_array) {
      if (defined $USERS{$uid}) {
        $USERS{$uid}->{VIS}=$level if ($level>0);
      }
    }
    $sth->finish;
  }
}

sub clear_user_list {
  $haveUSERS=0;
  %USERS=();
}

# fetch & cache group list
sub need_group_list {
  my ($gidr) = @_;
  my $sth;
  if (defined($gidr)) {
    return if (defined $GROUPS{$gidr});
    $sth=db_prepare("SELECT G.GID,G.DEFINER,G.NAME,G.DESCR,G.ISPUBLIC,G.MAX,G.MAXFORM,G.WWHEN FROM #GROUPS G WHERE (G.DEFINER=? OR EXISTS(SELECT 1 FROM #SHARES S WHERE S.UID=? AND S.GID=G.GID)) AND G.GID=? ORDER BY WWHEN");
    $sth->execute($auth_uid,$auth_uid,$gidr);
  } else {
    return if ($haveGROUPS);
    $sth=db_prepare("SELECT G.GID,G.DEFINER,G.NAME,G.DESCR,G.ISPUBLIC,G.MAX,G.MAXFORM,G.WWHEN FROM #GROUPS G WHERE (G.DEFINER=? OR EXISTS(SELECT 1 FROM #SHARES S WHERE S.UID=? AND S.GID=G.GID)) AND G.ISPUBLIC ORDER BY WWHEN");
    $sth->execute($auth_uid,$auth_uid);
    $haveGROUPS=1;
  }
  while (my ($gid,$definer,$name,$descr,$ispublic,$max,$maxform,$wwhen) = $sth->fetchrow_array) {
    $GROUPS{$gid}={GID => $gid, DEFINER => $definer, NAME => $name, DESCR => $descr || "",MAX=>$max==0 ? "" : $max,MAXFORM => $maxform,WWHEN=>$wwhen,PUBLIC=>$ispublic,DNAME=>$name."(".substr($wwhen,0,10).")"};
  }
}

# -1 is the admin user; return -2 for error
sub lookup_user {
  need_user_list;
  my ($prefix) = @_;
  my $uid;
  $prefix=lc(normalize_name($prefix));
  my $len=length($prefix);
  for my $name (keys %FUSERS) {
    if (length($name) >= $len && substr($name,0,$len) eq $prefix) {
      return $FUSERS{$name} if (length($name) == $len);
      if (!defined $uid || $FUSERS{$name}==$uid) {
        $uid=$FUSERS{$name};
      } else {
        return -2
      }
    }
  }
  return $uid;
}

# TODO: waarom werkt "3s = Samuel Van Reeth 20" ?
# TODO: naam die begint met $ is enkel een probleem als ze voor de rest enkel uit cijfers bestaat
# TODO: enige warning bij mode 2 wanneer expanden faalt door ambiguiteit? misschien toelaten namen te omgeven met {} in de plaats ofzo, met \ erbinnen geescapet
sub process_bill {
  my ($descr,$mode)=@_;  # mode=0 do nothing, 1: expand uid->names, 2: expand uid->names (and verify), 3: compact names->uid (and give warnings)
  my $ret="";
  my $err=0;
  my $cont=0;
  my $tot=0;
  my %short;
  my %contrib;
  my @effects;
  for my $line (split /\n/,$descr) {
    chomp $line;
    my $rline;
    my $suffix;
    my %eff=();
    $line =~ /\A(\s*)(.*?)(\s*)\Z/; # to be processed
    $rline .= $1; # already processed
    $line = $2;
    $suffix = $3; # chopped off at the end
    my $idx=index($line,'#');
    if ($idx >= 0) { # comment found, strip it
      $suffix = substr($line,$idx).$suffix;
      $line = substr($line,0,$idx);
    }
    $line =~ /\A(.*?)(\s*)\Z/;
    $line = $1;
    $suffix = $2 . $suffix;
    my $amount;
    if ($line =~ /\A(\*?\-?[0-9]+(?:\.[0-9]+)?)(\s*)(.*?)\Z/) { # strip of amount at beginning
      $amount=$1;
      $rline .= $1 . $2;
      $line=$3;
    }
    my $item;
    if ($line =~ /\A([^:]*?)(\s*:\s*)(.*?)\Z/) { # strip off item at beginning
      $item = $1;
      $rline .= $1 . $2;
      $line = $3;
    }
    my $def;
    if ($line =~ /\A([a-zA-Z][a-zA-Z0-9]*)?(\s*)=(\s*)(.*?)\Z/) { # strip off defined name at beginning
      $def = $1;
      $rline .= $1 . $2 . '=' . $3;
      $line = $4;
    }
    while ($line ne '') { # parse LDEFs
      $line =~ /\A([^,]*?)(?:(\s*,\s*)(.*?))?\Z/; # cut off comma-delimited part
      my $ldef = $1;
      $line = $3; $line="" if (!defined $line);
      my $intra = $2; $intra="" if (!defined $intra);
      my $rldef="";
      while ($ldef ne '') { # parse SDEFs
        my $count;
        if ($ldef =~ /\A([0-9]+)(\s+)(.*?)\Z/) {
          $count = $1;
          $rldef .= $1.$2;
          $ldef = $3;
        }
        my $pldef = $ldef;
        my ($rsdef,$sdef,$intra2);
        if (!defined $count) {
          $ldef =~ /\A([0-9]*)([^\s]*?)(?:(\s+)(.*?))?\Z/; # attempt to split rest of LDEF into [number]<SDEF> <rest>
          $count=$1 || 1;
          $rsdef=$1; $rsdef="" if (!defined $rsdef);
          $sdef = $2; $sdef="" if (!defined $sdef);
          $ldef = $4; $ldef="" if (!defined $ldef);
          $intra2 = $3; $intra2="" if (!defined $intra2);
        } else {
          $ldef =~ /\A([^\s]*?)(?:(\s+)(.*?))?\Z/; # attempt to split rest of LDEF into [number]<SDEF> <rest>
          $rsdef="";
          $sdef = $1; $sdef="" if (!defined $sdef);
          $ldef = $3; $ldef="" if (!defined $ldef);
          $intra2 = $2; $intra2="" if (!defined $intra2);
        }
        if (defined $short{lc($sdef)}) {
          my $ddef=$short{lc($sdef)};
          foreach my $uid (keys %{$ddef}) {
            $eff{$uid} += $ddef->{$uid}*$count;
          }
          $rldef .= $rsdef . $sdef . $intra2;
        } else {
          my $uid;
          my $sldef="";
          my $contrib;
          if ($pldef =~ /\A(.*?)(\s*)@(-?[0-9]+(?:\.[0-9]+)?)\Z/) {
            $sldef = $2 . '@' . $3;
            $contrib = $3;
            $pldef = $1;
          }
          if ($pldef =~ /\A\$([0-9]+)/) {
            $uid=$1;
            if ($mode==1) { # just expand uid into name
              need_user_list($uid);
              $pldef=$USERS{$uid}->{NAME};
            } elsif ($mode==2) { # expand uid into name, guaranteeing reversability
              need_user_list;
              my $fname=$USERS{$uid}->{NAME};
              if ($fname =~ /\A(.*?)(\s*)(@\-?[0-9]+(?:\.[0-9]+)?)\Z/) { $fname = $1; }
              if ($fname =~ /\A([^,]*?)\s*,/) { $fname = $1; }
              my $ruid=lookup_user($fname);
              if (defined $ruid && $uid==$ruid && (substr($fname,0,1) ne '$')) {
                $pldef = $fname;
              }
            }
          } else {
            $uid=lookup_user($pldef);
            if ($mode==3) {
              if (defined $uid && $uid!=-2 {
                $pldef = '$'.$uid;
              }
              if (defined $uid && $uid==-2 {
                push @msg,['warn',"Ambiguous user specification in bill: ".htmlwrap("'".$pldef."'") . (defined $item ? " (in definition of item ".htmlwrap("'".$item."'").")" : "")];
                $err=1;
              }
              if (!defined $uid) {
                push @msg,['warn',"Invalid user specification in bill: ".htmlwrap("'".$pldef."'") . (defined $item ? " (in definition of item ".htmlwrap("'".$item."'").")" : "")];
                $err=1;
              }
            }
          }
          if (defined $uid) {
            $eff{$uid}+=$count;
            $cont += $contrib if (defined $contrib);
            push @effects,[$uid,1,1,$contrib] if (defined $contrib);
          }
          $rldef .= $pldef . $sldef;
          last;
        }
      }
      $rline .= $rldef . $intra;
    }
    if (defined $def) {
      if (defined $short{lc($def)} && $mode==3) {
        push @msg,['warn',"Shorthand '".htmlwrap($def)."' is defined more than once."];
        $err=1;
      }
      $short{lc($def)} = \%eff;
    }
    if (defined $amount) {
      my $sum=0;
      if (substr($amount,0,1) eq '*') {
        $amount=substr($amount,1);
        $sum=1;
      } else {
        foreach my $uid (keys %eff) {
          $sum += $eff{$uid};
        }
      }
      foreach my $uid (keys %eff) {
        $tot += ($eff{$uid}*$amount)/$sum;
        push @effects,[$uid,-$eff{$uid},$sum,$amount,$item];
      }
    }
    $ret .= $rline . $suffix . "\n";
  }
  return ($ret,$err,$tot,$cont,@effects);
}


###########################
# transactional functions #
###########################

# these functions can only be called from within db_isolate

# change a password
sub tx_set_password {
  my ($key,$uid,$level)=@_;
  db_isolated;
  $uid=$auth_uid if (!defined $uid);
  $level=1 if (!defined $level);
  return 0 if (!defined $uid);
  my $sth=db_prepare("DELETE FROM #PWAUTH WHERE UID=?");
  $sth->execute($uid);
  $sth=db_prepare("INSERT INTO #PWAUTH (KEY,UID,LEVEL) VALUES (?,?,?)");
  $sth->execute($key,$uid,$level);
  return 1;
}

# modify htlogin
sub tx_set_htlogin {
  my ($htname,$uid,$level)=@_;
  db_isolated;
  $uid=$auth_uid if (!defined $uid);
  return 0 if (!defined $uid);
  my $sth=db_prepare("DELETE FROM #HTAUTH WHERE HTNAME=?");
  $sth->execute($htname);
  $sth=db_prepare("INSERT INTO #HTAUTH (HTNAME,UID,LEVEL) VALUES (?,?,?)");
  $sth->execute($htname,$uid,$level);
  return 1;
}

# create a user
sub tx_create_user {
  my ($user,$fullname,$email)=@_;
  db_isolated;
  my $sth=db_prepare("SELECT nextval('#NUSERS')");
  $sth->execute;
  my ($nuid)=$sth->fetchrow_array;
  $sth=db_prepare("INSERT INTO #USERS (UID,UNAME,FULLNAME,EMAIL,ACTIVE) VALUES (?,?,?,?,?)");
  my $ret=$sth->execute($nuid,$user,normalize_name($fullname),$email,0);
  if (defined $ret && $ret>0) {
    $sth=db_prepare("DELETE FROM #USERREQ WHERE UNAME=?");
    $sth->execute($user);
    $sth->finish;
    return $nuid;
  }
  return undef;
}

# recalculate the 'enabled' field
# only to be used when the transaction is not counted
sub tx_update_enabled {
  my ($tid) = @_;
  db_isolated;
  my $sth=db_prepare("UPDATE #EF E SET ENABLED=(SELECT (T.AUTHOR=E.UID OR (E.ACCEPT AND E.AMOUNT>E.SEEN-U.AUTOACCEPT)) FROM #USERS U, #TR T WHERE U.UID=E.UID AND T.TID=?) WHERE E.TID=?");
  $sth->execute($tid,$tid);
}

# include/exclude transaction from total view
sub tx_count_transaction {
  my ($tid,$count) = @_;
  db_isolated;
  my $sth=db_prepare("SELECT COUNTED FROM #TR T WHERE TID=?"); # check whether this transaction is already included in totals
  $sth->execute($tid);
  my ($cnt)=$sth->fetchrow_array;
  $cnt=($cnt ? 1 : 0);
  if ($cnt!=($count?1:0)) { # if this differs from the requested
    # retrieve some global information about the transaction
    $sth=db_prepare("SELECT T.AUTHOR, T.WWHEN FROM #TR T WHERE T.TID=?");
    $sth->execute($tid);
    my ($author,$wwhen)=$sth->fetchrow_array;
    # update the count field to reflect the requested inclusion
    $sth=db_prepare("UPDATE #TR SET COUNTED=? WHERE TID=?");
    $sth->execute($count?1:0,$tid);
    # update totals
    $sth=db_prepare("UPDATE #USERS U SET ". # first for affected people
      "TOTALSUM=U.TOTALSUM+((SELECT E.AMOUNT FROM #EF E WHERE E.UID=U.UID AND E.TID=?)*?)::NUMERIC(20,10), ".
      "TOTALPCT=U.TOTALPCT+((SELECT E.AMOUNT FROM #EF E WHERE E.UID=U.UID AND E.TID=?)*POW($PCT, EXTRACT(EPOCH FROM (U.CREATED - ?)) / $SEC_PER_YEAR)*?)::NUMERIC(20,10) ".
      "WHERE U.UID!=? AND U.UID IN (SELECT E.UID FROM #EF E WHERE E.TID=? AND E.ENABLED)"
    );
    $sth->execute($tid,$count?1:(-1),$tid,$wwhen,$count?1:(-1),$author,$tid);
    $sth=db_prepare("SELECT COALESCE(SUM(E.AMOUNT),0) FROM #EF E WHERE E.TID=? AND E.ENABLED AND E.UID!=?"); # then for the author
    $sth->execute($tid,$author);
    my ($teff) = $sth->fetchrow_array;
    $sth=db_prepare("UPDATE #USERS U SET ".
      "TOTALSUM=U.TOTALSUM-((?::NUMERIC(20,10))*?), ".
      "TOTALPCT=U.TOTALPCT-((?::NUMERIC(20,10))*POW($PCT, EXTRACT(EPOCH FROM (U.CREATED - ?)) / $SEC_PER_YEAR)*?) ".
      "WHERE U.UID=?"
    );
    $sth->execute($teff,$count?1:(-1),$teff,$wwhen,$count?1:(-1),$author);
    # update edges
    if ($count) {
      $sth=db_prepare("SELECT E.UID FROM #EF E WHERE E.TID=? AND NOT EXISTS(SELECT 1 FROM #EDGEINFO I WHERE I.ETO=E.UID AND I.EFROM=? AND I.ETYP='d')");
      $sth->execute($tid,$author); # make sure per-edge rows exist for the edges between author and affected ones
      my $sth2;
      while (my ($nuid) = $sth->fetchrow_array) {
        $sth2=db_prepare("INSERT INTO #EDGEINFO (ETO,EFROM,ETYP) VALUES (?,?,'d')") if (!defined $sth2); # by creating defaults if necessary
        $sth2->execute($nuid,$author) if ($nuid!=$author);
      }
      $sth=db_prepare("UPDATE #EDGEINFO I SET ". # and finally updating those
        "TOTALSUM=I.TOTALSUM+((SELECT E.AMOUNT FROM #EF E WHERE E.UID=I.ETO AND E.TID=?)*?)::NUMERIC(20,10), ".
        "TOTALPCT=I.TOTALPCT+((SELECT E.AMOUNT FROM #EF E WHERE E.UID=I.ETO AND E.TID=?)*POW($PCT, EXTRACT(EPOCH FROM (I.CREATED - ?)) / $SEC_PER_YEAR)*?)::NUMERIC(20,10) ".
        "WHERE I.EFROM=? AND I.EFROM!=I.ETO AND I.ETO IN (SELECT E.UID FROM #EF E WHERE E.TID=? AND E.ENABLED)"
      );
      $sth->execute($tid,$count?1:(-1),$tid,$wwhen,$count?1:(-1),$author,$tid);
    }
  }
  clear_user_list;
}

# process a request
sub tx_proc_req {
  my ($req)=@_;
  db_isolated;
  my $sth=db_prepare("DELETE FROM #USERREQ WHERE EXPIRE<CURRENT_TIMESTAMP");
  $sth->execute;
  $sth=db_prepare("SELECT UNAME,FULLNAME,ACCNR,EMAIL,HTNAME,PWKEY,LEVEL FROM #USERREQ WHERE RID=?");
  $sth->execute($req);
  my $sth2=db_prepare("UPDATE #USERS SET ACCNR=? WHERE UID=?");
  my $nuid;
  my $cnt=0;
  while (my ($username,$fullname,$accnr,$email,$htname,$pwkey,$level) = $sth->fetchrow_array) {
    $cnt++;
    $nuid=tx_create_user($username,$fullname,$email);
    tx_set_password($pwkey,$nuid,$level) if (defined $nuid && defined $pwkey);
    tx_set_htlogin($htname,$nuid,$level) if (defined $nuid && defined $htname);
    $sth2->execute($accnr,$nuid) if (defined $nuid && defined $accnr);
  }
  if ($cnt==0) {
    push @msg,['warn',"Invalid activation code. It may have been used already, or expired."];
  }
  return $nuid;
}

sub tx_change_accept {
  my ($uid,$am,$x,$tid) = @_;
  db_isolated;
  return if (!$auth_active);
  $am=0 if (!defined($am));
  $x=1 if (!defined($x));
  tx_count_transaction($tid,0);
  my $sth=db_prepare("UPDATE #EF SET ACCEPT=?, SEEN=? WHERE UID=? AND TID=?");
  $sth->execute($x,$am,$uid,$tid);
  tx_update_enabled($tid);
  tx_count_transaction($tid,1);
}

sub tx_delete_transaction {
  my ($tid,$typ) = @_;
  db_isolated;
  # verify the transaction can be safely removed
  my $sth=db_prepare("SELECT EXISTS(SELECT 1 FROM #EF E, #TR T WHERE E.TID=? AND T.TID=? AND E.SEEN!=0 AND E.ACCEPT=TRUE AND E.UID!=T.AUTHOR)");
  $sth->execute($tid,$tid);
  my ($cnt)=$sth->fetchrow_array;
  if ($cnt) {
    push @msg,['warn',"Cannot delete transaction. Please make sure the transaction has value zero, and that all people involved acknowledge it."];
    return 0;
  }
  # do not count transaction
  tx_count_transaction($tid,0);
  # effectively remove the transaction and all its effects
  if ($typ eq 'i') {
    $sth=db_prepare("DELETE FROM #ITEM WHERE TID=?");
    $sth->execute($tid);
  } elsif ($typ eq 'b') {
    $sth=db_prepare("DELETE FROM #BILL WHERE TID=?");
    $sth->execute($tid);
  }
  $sth=db_prepare("DELETE FROM #EF WHERE TID=?");
  $sth->execute($tid);
  $sth=db_prepare("DELETE FROM #TR WHERE TID=?");
  $sth->execute($tid);
  # delete orphan groups (TODO: speedup by only selecting groups which are affected by deleted transaction)
  $sth=db_prepare("SELECT G.GID FROM #GROUPS G WHERE G.ISPUBLIC=FALSE AND NOT EXISTS(SELECT 1 FROM #TR T WHERE T.AFG=G.GID)");
  $sth->execute;
  my $sth2=db_prepare("DELETE FROM #SHARES WHERE GID=?");
  my $sth3=db_prepare("DELETE FROM #GROUPS WHERE GID=?");
  while (my ($dgid) = $sth->fetchrow_array) {
    $sth2->execute($dgid);
    $sth3->execute($dgid);
  }
  return 1;
}

sub tx_calculate_effects {
  my ($tid) = @_;
  db_isolated;
  my @eff;
  tx_count_transaction($tid,0);
  my $sth=db_prepare("SELECT T.TYP,T.AFU,T.AFG,T.AUTHOR FROM #TR T WHERE T.TID=?");
  $sth->execute($tid);
  my ($typ,$afu,$afg,$author)=$sth->fetchrow_array;
  if (!defined $typ) {
    return 0; # transaction does not exist... nothing to update
  }
  if ($typ eq 'i') {  # ITEM
    if (defined $afu && defined $afg) {
      die "Inconsistent database: item $tid affects both user $afu and group $afg.";
    }
    if (!defined $afu && !defined $afg) {
      die "Inconsistent database: item $tid affects neither a user or a group.";
    }
    $sth=db_prepare("SELECT I.AMOUNT FROM #ITEM I WHERE I.TID=?");
    $sth->execute($tid);
    my ($am)=$sth->fetchrow_array;
    if (!defined $am) {
      die "Inconsistent databse: no item-specific data for transaction $tid.";
    }
    if (defined $afu) {
      push @eff,[$afu,-1,1,$am];
    } else {
      $sth=db_prepare("SELECT SUM(S.AMOUNT), G.MAX FROM #GROUPS G, #SHARES S WHERE G.GID=? AND S.GID=? GROUP BY G.MAX");
      $sth->execute($afg,$afg);
      my ($tot,$max) = $sth->fetchrow_array;
      $tot=0 if (!defined $tot);
      $max=0 if (!defined $max);
      $max=$tot if ($tot>$max);
      $sth=db_prepare("SELECT S.UID, S.AMOUNT FROM #SHARES S WHERE S.GID=?");
      $sth->execute($afg);
      while (my ($uid,$sh) = $sth->fetchrow_array) {
        push @eff,[$uid,-$sh,$max,$am];
      }
    }
  } elsif ($typ eq 'b') {
    $sth=db_prepare("SELECT B.DEFINITION FROM #BILL B WHERE B.TID=?");
    $sth->execute($tid);
    my ($def)=$sth->fetchrow_array;
    if (!defined $def) {
      die "Inconsistent database: no bill-specific data for transaction $tid.";
    }
    my ($ndef,$err,$tot,$cont,@effects)=process_bill($def,0);
    if (defined $ndef) {
      push @eff,@effects;
    } else {
      # TODO: warning ofzo, ongeldige bill
    }
  } else {
    die "Inconsistent database: transaction $tid has unknown type '$typ'.";
  }
  $sth=db_prepare("UPDATE #EF SET AMOUNT=0 WHERE TID=?"); # reset all effects to zero
  $sth->execute($tid);
  my $sth1=db_prepare("SELECT EXISTS(SELECT 1 FROM #EF WHERE TID=? AND UID=?)"); # check whether they exist
  my $sth2=db_prepare("INSERT INTO #EF (TID,UID,AMOUNT) VALUES(?,?,((?::NUMERIC(18,10))*?)/?)"); # if not, add them
  my $sth3=db_prepare("UPDATE #EF SET AMOUNT=AMOUNT+(((?::NUMERIC(18,10))*?)/?) WHERE TID=? AND UID=?"); # otherwise, update them
  for my $eff (@eff) {
    my ($uid,$num,$den,$am)=@{$eff};
    if ($uid != $author) {
      $sth1->execute($tid,$uid);
      my ($cnt)=$sth1->fetchrow_array;
      if ($cnt) { 
        $sth3->execute($am,$num,$den,$tid,$uid);
      } else {
        $sth2->execute($tid,$uid,$am,$num,$den);
      }
    }
  }
  $sth1->execute($tid,$author);
  my ($cnt)=$sth1->fetchrow_array;
  if ($cnt) {
    $sth=db_prepare("UPDATE #EF SET AMOUNT=COALESCE(-(SELECT SUM(E.AMOUNT) FROM #EF E WHERE E.TID=?),0) WHERE TID=? AND UID=?");
    $sth->execute($tid,$tid,$author);
  } else {
    $sth=db_prepare("INSERT INTO #EF (TID,UID,AMOUNT) VALUES (?,?,COALESCE(-(SELECT SUM(E.AMOUNT) FROM #EF E WHERE E.TID=?),0))");
    $sth->execute($tid,$author,$tid);
  }
  # delete irrelevant effects: value is zero (no net effect), and are either accepted+acknowledged or denied
  $sth=db_prepare("DELETE FROM #EF E WHERE E.TID=? AND E.AMOUNT=0 AND E.UID!=? AND (E.SEEN=0 OR NOT E.ACCEPT)");
  $sth->execute($tid,$author);
  tx_update_enabled($tid);
  tx_count_transaction($tid,1);
  return 1;
}

# level 0: totals
# level 1: enabled, totals
sub tx_recalculate {
  my ($level) = @_;
  db_isolated;
  # reset all totals to zero
  db_do("UPDATE #USERS SET TOTALSUM=0, TOTALPCT=0");
  db_do("UPDATE #EDGEINFO SET TOTALSUM=0, TOTALPCT=0");
  # mark all transactions as uncounted
  db_do("UPDATE #TR SET COUNTED=FALSE");
  # loop over all transactions
  my $sth=db_prepare("SELECT TID FROM #TR");
  $sth->execute;
  while (my ($tid) = $sth->fetchrow_array) {
    if ($level==0) { 
      # count_transaction will re-add the transaction to the totals
      tx_count_transaction($tid,1);
    } elsif ($level==1) {
      # recalculate the enabled field, and re-add
      tx_update_enabled($tid);
      tx_count_transaction($tid,1);
    } elsif ($level==2) {
      tx_calculate_effects($tid);
    }
  }
  # remove unnecessary edges
  db_do("DELETE FROM #EDGEINFO WHERE TOTALSUM=0 AND TOTALPCT=0");
}

sub tx_needtid {
  my ($a) = @_;
  db_isolated;
  if (!defined $a->{tid}) {
    my $sth=db_prepare("SELECT nextval('#NTR')");
    $sth->execute;
    $a->{tid} = $sth->fetchrow_array;
  }
}

sub tx_needgid {
  my ($a) = @_;
  db_isolated;
  if (!defined $a->{tid}) {
    my $sth=db_prepare("SELECT nextval('#NGROUPS')");
    $sth->execute;
    $a->{gid}=$sth->fetchrow_array;
  }
}

sub tx_accept {
  my ($tid,$uid) = @_;
  db_isolated;
  my $sth=db_prepare("SELECT AMOUNT FROM #EF WHERE TID=? AND UID=?");
  $sth->execute($tid,$uid);
  my ($amount)=$sth->fetchrow_array;
  if (defined $amount) {
    tx_change_accept($uid,$amount,1,$tid);
  }
}

sub tx_perform {
  my ($x,$a) = @_;
  db_isolated;
  if ($x eq 'pay_new') {
    tx_needtid($a);
    my $sth=db_prepare("INSERT INTO #TR (TID,AUTHOR,AFU,TYP) values (?,?,?,'i')");
    $sth->execute($a->{tid},$a->{actor},$a->{user});
    $sth=db_prepare("INSERT INTO #ITEM (TID,AMOUNT) values (?,?)");
    $sth->execute($a->{tid},-$a->{val});
    my $ret=tx_calculate_effects($a->{tid});
    return () if (!$ret);
    tx_accept($a->{tid},$a->{actor});
  } elsif ($x eq 'item_new') {
    tx_needtid($a);
    my $sth=db_prepare("INSERT INTO #TR (TID,AUTHOR,AFG,AFU,NAME,DESCR,TYP) VALUES (?,?,?,?,?,?,'i')");
    $sth->execute($a->{tid},$a->{actor},$a->{gid},$a->{uid},$a->{name},$a->{descr});
    $sth=db_prepare("INSERT INTO #ITEM (TID,AMOUNT) VALUES (?,?)");
    $sth->execute($a->{tid},$a->{value});
    my $ret=tx_calculate_effects($a->{tid});
    return () if (!$ret);
    tx_accept($a->{tid},$a->{actor});
  } elsif ($x eq 'bill_new') {
    tx_needtid($a);
    my $sth=db_prepare("INSERT INTO #TR (TID,AUTHOR,NAME,DESCR,TYP) VALUES (?,?,?,?,'b')");
    $sth->execute($a->{tid},$a->{actor},$a->{name},$a->{descr});
    $sth=db_prepare("INSERT INTO #BILL (TID,DEFINITION) VALUES (?,'')");
    $sth->execute($a->{tid});
    my $ret=tx_calculate_effects($a->{tid});
    return () if (!$ret);
    tx_accept($a->{tid},$a->{actor});
  } elsif ($x eq 'req_new') {
    my $sth=db_prepare("INSERT INTO #USERREQ (RID,UNAME,FULLNAME,ACCNR,EMAIL,HTNAME,PWKEY,LEVEL) VALUES (?,?,?,?,?,?,?,?)");
    $sth->execute($a->{rid},$a->{user},$a->{fullname},$a->{accnr},$a->{email},$a->{htname},$a->{key},1);
  } elsif ($x eq 'prof_edit') {
    my $sth=db_prepare("UPDATE #USERS SET FULLNAME=?, ACCNR=?, AUTOACCEPT=? WHERE UID=?");
    $sth->execute(normalize_name($a->{fullname}),$a->{accnr},$a->{axept},$a->{actor});
  } elsif ($x eq 'pass_edit') {
    tx_set_password($a->{key},$a->{actor},1);
  } elsif ($x eq 'ack_edit') {
    foreach my $ack (@{$a->{acks}}) {
      tx_change_accept($a->{actor},$ack->[1],$ack->[2],$ack->[0]);
    }
  } elsif ($x eq 'group_new') {
    tx_needgid($a);
    my $sth=db_prepare("INSERT INTO #GROUPS (GID,DEFINER,NAME) VALUES (?,?,?)");
    $sth->execute($a->{gid},$a->{actor},$a->{name});
  } elsif ($x eq 'group_edit') {
    my %ass;
    # combine existing group-entries with passed data
    my $sth=db_prepare("SELECT UID,FORMULA FROM #SHARES WHERE GID=?");
    $sth->execute($a->{gid});
    while (my ($uid,$form) = $sth->fetchrow_array) {
      my $calc=calc($form);
      $a->{ass}->{$uid}=[$form,$calc] if (!defined $a->{ass}->{$uid});
    }
    # calculate gcd
    my $gcd=int($DENOM*$a->{max}->[1]+0.5) || 0;
    foreach my $uid (keys %{$a->{ass}}) {
      my $val=int($DENOM*$a->{ass}->{$uid}->[1]+0.5);
      $gcd = ($gcd==0 ? $val : gcd($val,$gcd)) if ($val>0);
    }
    $gcd=1 if ($gcd<=0);
    # delete old entries
    $sth=db_prepare("DELETE FROM #SHARES WHERE GID=?");
    $sth->execute($a->{gid});
    # create new entries
    $sth=db_prepare("INSERT INTO #SHARES (GID,UID,FORMULA,AMOUNT) VALUES (?,?,?,?)");
    for my $uid (keys %{$a->{ass}}) {
      my $val=int(($DENOM*$a->{ass}->{$uid}->[1]+0.5)/$gcd);
      $sth->execute($a->{gid},$uid,$a->{ass}->{$uid}->[0],$val) if ($val>0);
    }
    # update group-wide data
    my $mmax=int($a->{max}->[1]*$DENOM+0.5)/$gcd; $mmax=0 if ($mmax<0);
    $sth=db_prepare("UPDATE #GROUPS SET NAME=?,DESCR=?,MAX=?,MAXFORM=?,ISPUBLIC=? WHERE GID=?");
    $sth->execute($a->{name},$a->{descr},$mmax,$a->{max}->[0],$a->{public},$a->{gid});
    # recalculate all dependent transactions
    my $sthx=db_prepare("SELECT TID FROM #TR WHERE AFG=?");
    $sthx->execute($a->{gid});
    while (my ($tid) = $sthx->fetchrow_array) {
      return () if (!tx_calculate_effects($tid));
    }
  } elsif ($x eq 'bill_del' || $x eq 'pay_del' || $x eq 'item_del') {
    my $sth=db_prepare("SELECT T.AUTHOR FROM #TR T WHERE T.TID=?");
    $sth->execute($a->{tid});
    my ($author) = $sth->fetchrow_array;
    if ($author != $a->{actor}) {
      push @msg,['warn',"Permission denied for deleting transaction."];
      return ();
    }
    return () if (!tx_delete_transaction($a->{tid},$x eq 'bill_del' ? 'b' : 'i'));
  } elsif ($x eq 'item_edit' || $x eq 'pay_edit') {
    my $sth=db_prepare("SELECT T.AUTHOR FROM #TR T, #ITEM I WHERE T.TID=? AND I.TID=? AND T.TYP='i'");
    $sth->execute($a->{tid},$a->{tid});
    my ($author)=$sth->fetchrow_array;
    return () if (!defined $author); # no such item, just ignore request?
    if ($author != $a->{actor}) {
      push @msg,['warn',"Permission denied for editing item/payment."];
      return ();
    }
    $sth=db_prepare("UPDATE #ITEM SET AMOUNT=? WHERE TID=?");
    $sth->execute($a->{val},$a->{tid});
    if (defined $a->{name} || defined $a->{descr}) {
      $sth=db_prepare("UPDATE #TR SET NAME=?, DESCR=? WHERE TID=?");
      $sth->execute($a->{name},$a->{descr},$a->{tid});
    }
    return () if (!tx_calculate_effects($a->{tid}));
    tx_accept($a->{tid},$a->{actor});
  } elsif ($x eq 'vis_edit') {
    my $sth=db_prepare("DELETE FROM #VISIBLE WHERE SEER=?");
    $sth->execute($a->{actor});
    $sth=db_prepare("DELETE FROM #VISIBLE WHERE SEEN=?");
    $sth->execute($a->{actor});
    $sth=db_prepare("INSERT INTO #VISIBLE (SEER,SEEN,LEVEL) VALUES (?,?,?)");
    foreach my $uid (@{$a->{vis}}) {
      $sth->execute($a->{actor},$uid,1);
      $sth->execute($uid,$a->{actor},1);
    }
  } elsif ($x eq 'bill_edit') {
    my $sth=db_prepare("SELECT T.AUTHOR FROM #TR T, #BILL B WHERE T.TID=? AND B.TID=? AND T.TYP='b'");
    $sth->execute($a->{tid},$a->{tid});
    my ($author)=$sth->fetchrow_array;
    return () if (!defined $author); # no such item, just ignore request?
    if ($author != $a->{actor}) {
      push @msg,['warn',"Permission denied for editing bill."];
      return ();
    }
    $sth=db_prepare("UPDATE #BILL SET DEFINITION=? WHERE TID=?");
    $sth->execute($a->{def},$a->{tid});
    $sth=db_prepare("UPDATE #TR SET NAME=?, DESCR=? WHERE TID=?");
    $sth->execute($a->{name},$a->{descr},$a->{tid});
    return () if (!tx_calculate_effects($a->{tid}));
    tx_accept($a->{tid},$a->{actor});
  } elsif ($x eq 'req_proc') {
    my $uid=tx_proc_req($a->{code});
    $a->{uid}=$uid;
  } elsif ($x eq 'db_recalc') {
    tx_recalculate($a->{level});
  } else {
    push @msg,['error',"Unknown action '$x' requested"];
    return ();
  }
  return 1;
}

sub tx_store_msg {
  my $sth=db_prepare("INSERT INTO #MSG (SID,MTYP,MSG) VALUES (?,?,?)");
  foreach my $msg (@msg) {
    $sth->execute($session,$msg->[0],$msg->[1]);
  }
  @msg=();
  return 1;
}

##############################################################################
# isolated transactions                                                      #
##############################################################################

sub perform {
  my ($action,%arg)=@_;
  $arg{actor}=$auth_uid if (defined $auth_uid);
  $arg{path}=join('/',@path);
  my $actstr="$action ".Dumper(\%arg);
  log_action("start: $actstr");
  my ($code,@ret) = db_isolate(\&tx_perform,$action,\%arg);
  $actstr="$action ".Dumper(\%arg);
  if ($code==0) {
    log_action("done: $actstr");
    return \%arg;
  } else {
    if ($code==1) {
      log_action("user_error: $actstr [$ret[0]]");
      push @msg,['error',"An error occurred while processing the request. Please notify the administrator."];
    } elsif ($code==2) {
      log_action("db_error [$ret[0]]: $actstr [$ret[1]]");
      push @msg,['error',"A database error occurred while processing the request. Please try again or notify the administrator."];
    } elsif ($code==3) {
      log_action("aborted: $actstr")
    }
    return undef;
  }
}

##############################################################################
# HTML functions                                                             #
##############################################################################

# calculate an HTML color for the wall of fame/shame
sub get_color {
  my ($extra,$bgR,$bgG,$bgB)=@_;
  my ($maxE,$minE)=($maxExtra,$minExtra);
  my @args=(
    [1,0,0,1],
    [1,1,0,0.5],
    [1,1,1,0],
    [0.5,1,0.5,0.5],
    [0,1,0,1]
#    [1,1,1],
#    [1,1,1]
  );
  my $x=2;
  if (!defined($extra) || $extra==0) {
    $x=2;
  } else {
    if ($extra>0) {
      if (!defined ($maxExtra) || $maxExtra<=0) {
        $x=4;
      } else {
        $x=($extra/$maxExtra*2)+2;
      }
    } else {
      if (!defined ($minExtra) || $minExtra>=0) {
        $x=0;
      } else {
        $x=2-($extra/$minExtra*2);
      }
    }
  }
  $x=0 if ($x<0);
  $x=4 if ($x>4);
  my $pos=int($x); $x-=$pos;
  my $r=(1-$x)*$args[$pos][0]+$x*($args[$pos+1][0] || 0);
  my $g=(1-$x)*$args[$pos][1]+$x*($args[$pos+1][1] || 0);
  my $b=(1-$x)*$args[$pos][2]+$x*($args[$pos+1][2] || 0);
  my $a=(1-$x)*$args[$pos][3]+$x*($args[$pos+1][3] || 0);
  my $R=$r*$a+(($bgR)/255)*(1-$a);
  my $G=$g*$a+(($bgG)/255)*(1-$a);
  my $B=$b*$a+(($bgB)/255)*(1-$a);
  my $ret=sprintf("#%02x%02x%02x",int($R*255.995),int($G*255.995),int($B*255.995));
  return $ret;
}

sub htmlwrap {
  my ($v,$textarea)=@_;
  $v=encode_entities(decode('utf8',$v));
  $v =~ s/[\n]/<br\/>/gm if (!defined $textarea);
  return $v;
}

sub xmlwrap {
  my ($v)=@_;
  return (HTML::Entities::encode_entities_numeric($v,"\000\001\002\003\004\005\006\007\010\011\012\013\014\015\016\017\020\021\022\023\024\025\026\027\030\031\032\033\034\035\036\037\"'<>&"));
}

# some forms
sub show_form_add_pay {
  return if (!$auth_active);
  need_user_list;
  print "<h3>New payment:</h3>\n";
  print "<form action='".selfurl."' method='post'>\n";
  print "<p><input type='hidden' name='cmd' value='addpay' /></p>\n";
  print "<table>\n";
  print "<tr class='tblodd'><td>User</td><td></td><td> <select name='ap_user'>\n";
  for (sort {lc($a->{NAME}) cmp lc($b->{NAME})} (values %USERS)) {
    print "  <option value='$_->{UID}'>".htmlwrap($_->{NAME})."</option>\n" if (defined($_->{VIS}) && $_->{ACTIVE} && $_->{UID}!=$auth_uid);
  }
  print "</select></td></tr>\n";
  print "<tr class='tbleven'><td>paid me</td><td>$UNIT</td><td><input type='text' name='ap_value' value='0.00' /></td></tr>\n";
  print "</table>\n";
  print "<p><input type='submit' value='Add payment' /></p></form>\n";
}
sub show_form_add_bill {
  return if (!$auth_active);
  print "<h3>New bill:</h3>\n";
  print "To learn more about bills, see the <a href='".genurl('help','bill')."'>help</a> pages\n";
  print "<form action='".selfurl."' method='post'>\n";
  print "<p><input type='hidden' name='cmd' value='addbill' /></p>\n";
  print "<table>\n";
  print "<tr class='tblodd'><td>I paid a bill</td><td><input type='text' name='ab_name' /></td><td>(name)</td></tr>\n";
  print "<tr class='tbleven'><td>with description:</td><td> <input type='text' name='ab_descr' value='' /></td><td></td></tr>\n";
  print "</table>\n";
  print "<p><input type='submit' value='Add bill' /></p>\n";
  print "</form>";
}
sub show_form_add_item {
  return if (!$auth_active);
  need_user_list;
  need_group_list;
  print "<h3>New item:</h3>\n";
  print "<form action='".selfurl."' method='post' >\n";
  print "<p><input type='hidden' name='cmd' value='addwant' /></p>\n";
  print "<table>\n";
  print "<tr class='tblodd'><td>I paid </td><td>$UNIT</td><td><input type='text' name='aw_value' value='0.00' /></td><td>(price)</td></tr>\n";
  print "<tr class='tbleven'><td>on </td><td></td><td><input type='text' name='aw_name' value='' /></td><td>(name of item)</td></tr>\n";
  print "<tr class='tblodd'><td>with description:</td><td></td><td> <input type='text' name='aw_descr' value='' /></td><td></td> </tr>\n";
  print "<tr class='tbleven'><td>for user:</td><td><input type='radio' name='aw_gtype' value='user' checked='checked' id='aw_gt_user' /></td><td> <select name='aw_user' onchange='document.getElementById(\"aw_gt_user\").checked=true;' >\n";
  for (sort {lc($a->{NAME}) cmp lc($b->{NAME})} (values %USERS)) {
    print "  <option value='$_->{UID}'>".htmlwrap($_->{NAME})."</option>\n" if (defined($_->{VIS}) && $_->{ACTIVE} && $_->{UID}!=$auth_uid);
  }
  print "</select></td><td></td></tr>\n";
  print "<tr class='tblodd'><td>for new group:</td><td><input type='radio' name='aw_gtype' value='new' id='aw_gt_ng' /></td><td> <input type='text' name='aw_ng_name' onchange='document.getElementById(\"aw_gt_ng\").checked=true;' /></td><td></td></tr>\n";
  print "<tr class='tbleven'><td>for existing group:</td><td><input type='radio' name='aw_gtype' value='old' id='aw_gt_eg' /></td><td> <select name='aw_group' onchange='document.getElementById(\"aw_gt_eg\").checked=true;' >\n";
  for (sort {$GROUPS{$b}->{WWHEN} cmp $GROUPS{$a}->{WWHEN}} (keys %GROUPS)) {
    if ($GROUPS{$_}->{PUBLIC}) { print "  <option value='$GROUPS{$_}->{GID}'>".htmlwrap($GROUPS{$_}->{DNAME})."</option>\n" };
  }
  print "</select></td><td></td></tr>";
  print "</table>\n";
  print "<p><input type='submit' value='Add item' /></p>\n";
  print "</form>";
}
sub show_totals {
  my $sum=0;
  my $imneg=0;
  need_user_list;
  print "<p><span style=\"font-size:small;\">The colors are an indication of your account history: red means mostly negative, green mostly positive</span></p>\n";
  # By ruben: proberen om te laten zien hoe lang je nog op huidig bedrag moet staan om op neutraal te komen
  for (values %USERS) {
    if ($_->{UID} == $auth_uid) {
      my $t=$_->{TOTAL};
      my $e=$_->{EXTRA};
      if (defined ($t) && defined($e)) {
        $imneg=1 if ($t+$e<0);
        if ($t+$e!=0 && ($t/($t+$e))>0) {
          my $days=days_to_neutral($t,$e);
          if ($days >= 2) {
            print "<p>Within ".sprintf("%.0f", $days)." days your ".($e<0 ? "red" : "green")." color will become white, if no transactions occur</p>\n";
            print "<!-- TOTAL: $_->{TOTAL} ; EXTRA: $_->{EXTRA} -->";
          } if ($days <= -2) {
            print "<!-- You are ".sprintf("%.0f", -$days)." days beyond neutral. ".($t+$e>0 ? "Accept some money from others!" : "Give some money to others!")." -->\n";
            print "<!-- TOTAL: $_->{TOTAL} ; EXTRA: $_->{EXTRA} -->";
          }
        }
      }
    }
  }
  print "<div style=\"padding-right: 2em; float:left;\">\n";
  print "<h3>Hall of shame:</h3>";
  print "<table id='hos'>";
  print "<tr class='tblhead'><th>Name</th><th>Total</th></tr>\n";
  for (sort {$a->{ORD} <=> $b->{ORD}} (grep { defined($_->{ORD}) && $_->{ORD}<0 } (values %USERS))) {
    if ($_->{UID}==$auth_uid || ((defined $_->{VIS}) && $_->{ACTIVE})) {
      my $accnr = (defined $_->{ACCNR}) ? " accnr=$_->{ACCNR}" : "";
      if ($_->{TOTAL}>=0.05 || $_->{TOTAL}<=-0.05 || $_->{UID}==$auth_uid) {
        my ($hi1,$hi2)=("","");
        if (defined($auth_uid) && ($_->{UID} == $auth_uid)) {
          ($hi1,$hi2)=("<b>","</b>");
        }
        my $ab="";
        print "<tr class='tblunif'><td>$hi1".htmlwrap($_->{NAME})."$hi2</td><td style=\"text-align:right; background-color:".get_color($_->{EXTRA},226,226,226).";\">$hi1".( sprintf("$UNIT%.2f",$_->{TOTAL}))."<!-- + ".sprintf("%.4f",$_->{EXTRA})."; ".sprintf("%.0f",days_to_neutral($_->{TOTAL},$_->{EXTRA}))." days$accnr -->$hi2</td>$ab</tr> \n";
      } else {
        print "<!-- ".htmlwrap($_->{NAME}).": total=".sprintf("$UNIT%.2f",$_->{TOTAL})." int=".sprintf("%.4f",$_->{EXTRA})."$accnr -->\n";
      }
    }
    $sum += $_->{TOTAL};
  }
  my $shame=$sum;
  print "</table>\n";
  print "</div>\n";
  print "<div style=\"float:left;\">\n";
  print "<h3>Hall of fame:</h3>";
  print "<table id='hof'>";
  print "<tr class='tblhead'><th>Name</th><th>Total</th></tr>\n";
  for (sort {$b->{ORD} <=> $a->{ORD}} (grep { defined($_->{ORD}) && $_->{ORD}>=0 } (values %USERS))) {
    if ($_->{UID}==$auth_uid || ((defined $_->{VIS}) && $_->{ACTIVE})) {
      my $accnr = (defined $_->{ACCNR}) ? " accnr=$_->{ACCNR}" : "";
      if ($_->{TOTAL}>=0.05 || $_->{TOTAL}<=-0.05 || $_->{UID}==$auth_uid) {
        my ($hi1,$hi2)=("","");
        if (defined($_->{UID}) && $_->{UID} == $auth_uid) {
          ($hi1,$hi2)=("<b>","</b>");
        }
        my $ab="";
        print "<tr class='tblunif'><td>$hi1".htmlwrap($_->{NAME})."$hi2</td><td style=\"text-align:right; background-color:".get_color($_->{EXTRA},226,226,226).";\">$hi1".( sprintf("$UNIT%.2f",$_->{TOTAL}))."<!-- + ".sprintf("%.4f",$_->{EXTRA})."; ".sprintf("%.0f",days_to_neutral($_->{TOTAL},$_->{EXTRA}))." days$accnr -->$hi2</td>$ab</tr> \n";
      } else {
        print "<!-- ".htmlwrap($_->{NAME}).": total=";
        print sprintf("$UNIT%.2f",$_->{TOTAL});
        if (defined($_->{EXTRA})) {print " int=".sprintf("%.4f",$_->{EXTRA});}
        print "$accnr -->\n";
      }
    }
    $sum += $_->{TOTAL};
  }
  #print "<tr><td><em>Unassigned</em></td><td>".sprintf("$UNIT%.2f",$sum)."</td></tr>\n" if ($sum>=0.005);
  print "</table>\n";
  print "</div>\n";
  print "<div style=\"clear:both; margin-bottom: 2ex;\"><br/></div>\n";
  print "<p><b>Total imbalance: ".sprintf("$UNIT%.2f",-$shame)."</b></p>\n";
  print "<p style=\"margin-top: 2ex;\" />";
}

sub show_unassigned {
  return if (!defined $auth_username);
#  my $sth=db_prepare("SELECT SUM(U.VALUE) FROM #UNASS U, #WANT W WHERE W.WID=U.WID AND (W.WANTER=? OR (SELECT COUNT(*) FROM #SHARES S WHERE S.GID=W.WANTED AND S.UID=? AND S.AMOUNT!=0)>0)");
#  $sth->execute($auth_uid,$auth_uid);
#  my ($sum)=$sth->fetchrow_array;
#  $sth=db_prepare("SELECT U.NAME,U.VALUE,U.WID,U.GID,U.UNASS,U.MAX FROM #UNASS U, #WANT W WHERE W.WID=U.WID AND (W.WANTER=? OR (SELECT COUNT(*) FROM #SHARES S WHERE S.GID=W.WANTED AND S.UID=? AND S.AMOUNT!=0)>0)");
#  $sth->execute($auth_uid,$auth_uid);
#  my $cnt=0;
#  while (my ($name,$value,$wid,$gid,$unass,$max) = $sth->fetchrow_array) {
#    if ($cnt==0) {
#      print "<h3>Unassigned (".sprintf("$UNIT%.2f",$sum).")</h3>\n";
#      print "<table>";
#      print "<tr class='tblhead'><th>Name</th><th>Value</th><th>Left</th><th>Assign</th></tr>\n";
#    }
#    $cnt++;
#    print "<tr class='".($cnt%2 ? "tblodd" : "tbleven")."'><td><a href='".genurl('item',$wid)."'>".htmlwrap($name || '-')."</a></td><td>".sprintf("EUR %.2f",$value)."</td><td>$unass/$max</td><td><a href='".genurl('group',$gid)."'>assign</a></td></tr>\n";
#  }
#  if ($cnt>0) {
#    print "</table>\n<p>";
#  }
#  return $cnt;
}

sub show_change_settings {
  return if (!defined $auth_username);
  my $sth=db_prepare("SELECT U.UNAME, U.FULLNAME, U.ACCNR, U.EMAIL, U.TOTALSUM, U.CREATED, U.AUTOACCEPT FROM #USERS U WHERE UID=?");
  $sth->execute($auth_uid);
  my ($uname,$fullname,$accnr,$email,$total,$created,$autoaccept)=$sth->fetchrow_array;
  print "<h3>Profile settings:</h3>\n";
  print "<form action='".selfurl."' method='post'>\n";
  print "<table>";
  print "<tr class='tblodd'><td>User name:</td><td></td><td>".htmlwrap($uname)."</td></tr>\n";
  print "<tr class='tbleven'><td>Full name:</td><td></td><td><input type='text' name='cp_fullname' value='".htmlwrap($fullname)."' /></td></tr>\n";
  print "<tr class='tblodd'><td>Bank account number:</td><td></td><td><input type='text' name='cp_accnr' value='".htmlwrap($accnr)."' /></td></tr>\n";
  print "<tr class='tbleven'><td>By default, deny charges above:</td><td></td><td><input type='text' size='7' name='cp_autoaccept' value='".htmlwrap($autoaccept)."' /> EUR</td></tr>\n";
  print "<tr class='tblodd'><td>E-mail address:</td><td></td><td>".htmlwrap($email)."</td></tr>\n";
  print "<tr class='tbleven'><td>Account balance:</td><td></td><td style='color:".($total>=0 ? 'black' : 'red')."'>".sprintf("$UNIT %.4f",abs($total))."</td></tr>\n";
  print "<tr class='tblodd'><td>Creation date:</td><td></td><td>".htmlwrap(substr($created,0,16))."</td></tr>\n";
  print "</table>\n";
  print "<p><input type='hidden' name='cmd' value='chprof' />\n";
  print "<input type='submit' value='Change settings' /></p>\n";
  print "</form>\n";
}

sub show_change_password {
  print "<h3>Change password:</h3>\n";
  print "<form action='".selfurl."' method='post'>\n";
  print "<table>";
  print "<tr class='tblodd'><td>Old password </td><td><input type='password' name='password' size='10' /></td></tr>\n";
  print "<tr class='tbleven'><td>New password: </td><td><input type='password' name='newpass1' size='10' /></td></tr>\n";
  print "<tr class='tblodd'><td> Repeat: </td><td><input type='password' name='newpass2' size='10' /></td></tr>\n";
  print "</table>\n";
  print "<p><input type='hidden' name='cmd' value='chpass' />\n";
  print "<input type='hidden' name='username' value='".(htmlwrap($auth_username))."' />\n";
  print "<input type='submit' value='Change password' /></p>\n";
  print "</form>\n";
}

sub describe {
  my ($amount,$name,$author,$affectuid,$affectgid,$type,$tid) = @_;
  need_group_list($affectgid) if (defined $affectgid);
  my $affectname;
  if (defined $affectuid) {
    if ($affectuid==$auth_uid) { $affectname="/me" } else {
      $affectname=htmlwrap($USERS{$affectuid}->{NAME});
    }
  } elsif (defined $affectgid) {
    need_group_list($affectgid);
    $affectname="<a href=\"".genurl('group',$affectgid)."\">".htmlwrap($GROUPS{$affectgid}->{NAME} || "group")."</a>";
  }
  my $actorname;
  if ($author==$auth_uid) { 
    $actorname="/me";
  } else {
    $actorname=htmlwrap($USERS{$author}->{NAME});
  }
  if ((($auth_uid==$author && $amount<0) || ($auth_uid!=$author && $amount>0)) && defined $affectuid) {
    my $sw=$affectname;
    $affectname=$actorname;
    $actorname=$sw;
    $amount = -$amount;
  }
  $actorname = 'I' if (defined $actorname && $actorname eq '/me');
  $affectname = 'me' if (defined $affectname && $affectname eq '/me');
  if ($type eq 'i') {
    if (!defined $name && defined $affectuid) {
      return $actorname . " <a href=\"".genurl('payment',$tid)."\">paid</a> " .(defined $affectname ? $affectname : "someone");
    } else {
      return $actorname . " paid <a href=\"".genurl('item',$tid)."\">" . (htmlwrap($name || 'nameless item')) . "</a> for " . (defined $affectname ? $affectname : "someone");
    }
  } elsif ($type eq 'b') {
    return $actorname . " paid <a href=\"".genurl('bill',$tid)."\">" . htmlwrap($name || 'nameless bill')."</a>";
  } else {
    return $actorname . " paid class-$type UFO ".htmlwrap($name || 'from outer space')." for ".(defined $affectname ? $affectname : "someone");
  }
}

# mode:
# 0: detail/history
# 1: changed
sub show_history_line {
  my ($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid,$num,$mode) = @_;
  print "<tr class='".($num%2 ? "tbleven" : "tblodd")."' ><td>";
  print (substr($wwhen,0,16) || "never");
  print "</td><td>";
  my $descr=describe($amount,$name,$author,$affectuid,$affectgid,$type,$tid);
  print $descr;
  print "</td><td style='text-align:right; color:".($amount>=0 ? 'black' : 'red')."'>";
  print "<a title=\"".htmlwrap($amount)."\">".sprintf("$UNIT%.2f",abs($amount))."</a>\n";
  my $raccept=($accept && $amount>$seen-$auth_autoaccept)||($author==$auth_uid);
  my $changed=abs($amount-$seen)>=$THRESHOLD;
  print "<input type='hidden' name='hlv_$tid' value='".($mode==1 ? $amount : $seen)."' />";
  print "<input type='hidden' name='hlo_$tid' value='".(($mode==1 && $changed) ? "r" : ($accept ? "" : "d"))."' />";
  print "</td>";
  if ($mode==1) {
    my $color=$amount>=$seen ? 'black' : 'red';
    print "<td style='text-align:right; color:$color'>";
    if ($changed) {
      if ($seen==0) {
        print "NEW";
      } else {
        print sprintf("$UNIT %.2f",abs($amount-$seen));
      }
    }
    print "</td>";
    print "<td><span><input type='radio' name='hlx_$tid' value='p' /></span><span style='background: #00FF00;'><input type='radio' name='hlx_$tid' value='a!' /></span><span style='background: #FF0000;'><input type='radio' name='hlx_$tid' value='a!' /></span></td>";
#    print "<td style='text-align: center;'><input type='radio' name='hlx_$tid' value='a' ".($raccept ? "checked='checked'" : '')." ".                                                "/></td>";
#    print "<td style='text-align: center;'><input type='radio' name='hlx_$tid' value='d' ".                                    " ".($author==$auth_uid ? 'disabled="disabled"' : '')."/></td>";
  } elsif ($mode==0) {
    print "<td style='text-align: center;'><input type='checkbox' name='hlx_$tid' value='d' ".($accept ? '' : "checked='checked'")." ".($author==$auth_uid ? 'disabled="disabled"' : '')."/></td>";
  } elsif ($mode==2) {
    my $sth=db_prepare("SELECT EE.UID, EE.AMOUNT, EE.ACCEPT FROM #EF EE WHERE EE.TID=? AND NOT EE.ENABLED AND EE.UID!=?");
    $sth->execute($tid,$author);
    my $sum=0;
    my @usd;
    my @usw;
    while (my ($uuid,$am,$acc) = $sth->fetchrow_array) {
      push @usd,$USERS{$uuid}->{NAME} if (!$acc);
      push @usw,$USERS{$uuid}->{NAME} if ( $acc);
      $sum += $am;
    }
    my $ramount=$amount+$sum;
    print "<td style='text-align:right; color:".($ramount>=0 ? 'black' : 'red')."'>";
    print "<a title=\"".htmlwrap($ramount)."\">".sprintf("$UNIT%.2f",abs($ramount))."</a>\n";
    print "</td>";
    print "<td>".(join(', ',map { htmlwrap($_) } @usw))."</td>";
    print "<td>".(join(', ',map { htmlwrap($_) } @usd))."</td>";
  }
  print "</tr>\n";
  return "$tid";
}

sub show_self_denied {
  need_user_list;
  my $sth=db_prepare("SELECT E.AMOUNT,E.SEEN,E.ACCEPT,T.NAME,T.AUTHOR,T.AFU,T.AFG,T.WWHEN,T.TYP,T.TID FROM #EF E, #TR T WHERE E.UID=? AND T.AUTHOR=E.UID AND T.TID=E.TID AND EXISTS(SELECT 1 FROM #EF EE WHERE EE.TID=T.TID AND NOT EE.ENABLED) ORDER BY WWHEN DESC");
  $sth->execute($auth_uid);
  my $warned=0;
  my $num=0;
  my @ids=();
  print "<h3>Not fully accepted transactions</h3>\n";
  while (my ($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid) = $sth->fetchrow_array) {
    if (!$warned) {
      print "<table>";
      print "<tr class='tblhead'><th>Date</th><th>Reason</th><th>Amount</th><th>Effective</th><th>Pending accept by</th><th>Denied by</th></tr>\n";
      $warned=1;
    }
    push @ids,show_history_line($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid,$num++,2);
  }
  if ($warned) {
    print "</table>\n";
  } else {
    print "None at this time.\n";
  }
  print "\n";
  return 1;
}

sub show_denied {
  need_user_list;
  my $sth=db_prepare("SELECT E.AMOUNT,E.SEEN,E.ACCEPT,T.NAME,T.AUTHOR,T.AFU,T.AFG,T.WWHEN,T.TYP,T.TID FROM #EF E, #TR T WHERE E.UID=? AND T.AUTHOR=E.UID AND T.TID=E.TID AND EXISTS(SELECT 1 FROM #EF EE WHERE EE.TID=T.TID AND NOT EE.ENABLED) ORDER BY WWHEN DESC");
  $sth->execute($auth_uid);
  my $warned=0;
  my $num=0;
  my @ids=();
  print "<h3>Not fully accepted transactions</h3>\n";
  while (my ($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid) = $sth->fetchrow_array) {
    if (!$warned) {
      print "<table>";
      print "<tr class='tblhead'><th>Date</th><th>Reason</th><th>Amount</th><th>Effective</th><th>Pending accept by</th><th>Denied by</th></tr>\n";
      $warned=1;
    }
    push @ids,show_history_line($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid,$num++,2);
  }
  if ($warned) {
    print "</table>\n";
  } else {
    print "None at this time.\n";
  }
  print "\n";
  return 1;
}

sub show_warn {
  need_user_list;
  my $sth=db_prepare("SELECT E.AMOUNT,E.SEEN,E.ACCEPT,T.NAME,T.AUTHOR,T.AFU,T.AFG,T.WWHEN,T.TYP,T.TID FROM #EF E, #TR T WHERE E.UID=? AND T.TID=E.TID AND ABS(E.AMOUNT-E.SEEN)>=? ORDER BY WWHEN DESC");
  $sth->execute($auth_uid,$THRESHOLD);
  my $warned=0;
  my $changes=0;
  my $num=0;
  my @ids=();
  print "<h3>Modified transactions</h3>\n";
  while (my ($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid) = $sth->fetchrow_array) {
    if (!$warned) {
      print "<form action='".selfurl."' method='post'>\n";
      print "<table>";
      print "<tr class='tblhead'><th>Date</th><th>Reason</th><th>Amount</th><th>Changed</th><th>Accepted</th></tr>\n";
      $warned=1;
    }
    push @ids,show_history_line($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid,$num++,1);
    if (abs($seen-$amount)>$THRESHOLD) {
      $changes++;
    }
  }
  if ($warned) {
    print "</table>\n";
    print "<div><input type='hidden' name='hl_ids' value='".join(',',@ids)."' />\n";
    print "<input type='hidden' name='cmd' value='dohl' />\n";
    print "<input type='submit' value='Acknowledge' /></div>\n";
    print "</form>\n";
  } else {
    print "None at this time.\n";
  }
  print "\n";
  return 1;
}


sub show_history {
  my ($all)=@_;
  my $sth;
  need_user_list;
  if ($all) {
    print "<h3>Full history</h3>\n";
  } else {
    print "<h3>Recent history</h3>\n";
  }
  print "<form action='".selfurl."' method='post'>\n";
  print "<table>";
  print "<tr class='tblhead'><th>Date</th><th>Reason</th><th>Amount</th><th>Denied</th></tr>\n";
  $sth=db_prepare("SELECT E.AMOUNT,E.SEEN,E.ACCEPT,T.NAME,T.AUTHOR,T.AFU,T.AFG,T.WWHEN,T.TYP,T.TID FROM #EF E, #TR T WHERE E.UID=? AND T.TID=E.TID ORDER BY T.WWHEN DESC".($all ? "" : " LIMIT 50"));
  $sth->execute($auth_uid);
  my @ids=();
  my $num=0;
  while (my ($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid) = $sth->fetchrow_array) {
    push @ids,show_history_line($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid,$num++,0);
  }
  $sth->finish;
  print "</table>";
  print "<div><input type='hidden' name='hl_ids' value='".join(',',@ids)."' />\n";
  print "<input type='hidden' name='cmd' value='dohl' />\n";
  print "<input type='submit' value='Change denies' /></div>\n";
  print "</form>\n";
  print "<br/>\n";
}

# calculate number of days to reach white
sub days_to_neutral {
  my ($t,$e) = @_;
  return 0 if ($t+$e==0);
  if ($t/($t+$e)>0) {
    return log($t/($t+$e))/log($PCT)*365.25;
  } else {
    return 0;
  }
}

# retrieve cookies to set (will be used in html headers and redirects)
sub get_cookies {
  my @cookies=();
  if (defined $session) {
    my %cookiedata=(-name => 'session', -value => $session, -domain => $ENV{HTTP_HOST}, -path => $DIR, -expires => "+${SESSION_TIME}m");
    push @cookies,cookie(%cookiedata);
  }
  return @cookies;
}

# output html header
sub output_header {
  my @cookies=get_cookies;
  print header(-cookie => \@cookies,-charset=>'UTF-8',-type => 'text/html');
  print "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\n";
  print "<html xmlns=\"http://www.w3.org/1999/xhtml\" xml:lang=\"en\" lang=\"en\" >\n";
  print "<head>\n";
  print "<meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\" />\n";
  print "<link rel='alternate' type=\"application/rss+xml\" title='RSS' href='".genurl('rss')."' />\n";
  print "<link rel='stylesheet' type=\"text/css\" href='$DIR/kas.css' />\n";
  print "<script type=\"text/javascript\" src=\"$DIR/kas.js\"></script>\n";
  print "<title>$title".(defined $auth_username ? (" - ".htmlwrap($auth_fullname)) : "")."</title>\n";
  print "</head>\n";
  print "<body>\n";
  print "<div id='kaslogo'><a href=\"$URL\">$htmltitle</a></div>\n";
  print "<div id='kashead'>";
  print "Logged in as ".htmlwrap($auth_fullname)." (".htmlwrap($auth_username).") <br/>" if (defined $auth_username);
  print "</div>\n";
  print "<table width='100%' cellspacing='0' cellpadding='0'><tr>";
  print "<td id='kasside' style='vertical-align:top;'><ul>\n";
  print "<li ".($path[0] eq 'overview' ? 'class="hilight"' : '')."><a accesskey=\"o\" href=\"".genurl('overview')."\">Overview</a></li>\n" if (defined $auth_username);
  print "<li ".($path[0] eq 'warn' ? 'class="hilight"' : '')."><a accesskey=\"w\" href=\"".genurl('warn')."\">Notifications</a></li>\n" if (defined $auth_username);
  print "<li ".($path[0] eq 'add' ? 'class="hilight"' : '')."><a accesskey=\"a\" href=\"".genurl('add')."\">New transaction</a></li>\n" if (defined $auth_username);
  print "<li ".($path[0] eq 'connections' ? 'class="hilight"' : '')."><a accesskey=\"c\" href=\"".genurl('connections')."\">Connections</a></li>\n" if (defined $auth_username);
  print "<li ".($path[0] eq 'history' ? 'class="hilight"' : '')."><a accesskey=\"h\" href=\"".genurl('history')."\">Full history</a></li>\n" if (defined $auth_username);
  print "<li ".($path[0] eq 'payment' ? 'class="hilight"' : '')."><a href=\"".selfurl."\">Payment</a></li>" if (defined $auth_username && $path[0] eq 'payment');
  print "<li ".($path[0] eq 'item' ? 'class="hilight"' : '')."><a href=\"".selfurl."\">Item</a></li>" if (defined $auth_username && $path[0] eq 'item');
  print "<li ".($path[0] eq 'group' ? 'class="hilight"' : '')."><a href=\"".selfurl."\">Group</a></li>" if (defined $auth_username && $path[0] eq 'group');
  print "<li ".($path[0] eq 'bill' ? 'class="hilight"' : '')."><a href=\"".selfurl."\">Bill</a></li>" if (defined $auth_username && $path[0] eq 'bill');
  print "<li ".($path[0] eq 'settings' ? 'class="hilight"' : '')."><a accesskey=\"s\" href=\"".genurl('settings')."\">Settings</a></li>\n" if (defined $auth_username);
  print "<li>&nbsp;</li>\n";
  print "<li ".($path[0] eq 'activate' ? 'class="hilight"' : '')."><a href=\"".selfurl."\">Account activation</a></li>" if (defined $path[0] && $path[0] eq 'activate');
  print "<li ".($path[0] eq 'help' ? 'class="hilight"' : '')."><a accesskey=\"?\" href=\"".genurl((defined $path[0] && $path[0] eq 'help') ? 'help' : ('help',@path))."\">Help</a></li>\n";
  print "<li>&nbsp;</li>\n";
  print "<li ".($path[0] eq 'logout' ? 'class="hilight"' : '')."><a accesskey=\"x\" href=\"".genurl('logout')."\">Log out</a></li>\n" if (defined $auth_username || defined $session);
  print "<li ".($path[0] eq 'login' ? 'class="hilight"' : '')."><a href=\"".genurl('login')."\">Log in</a></li>\n" if ((defined $path[0] && $path[0] eq 'login') || !defined $auth_username);
  print "</ul></td>\n";
  print "<td id='kasbody' style='vertical-align:top;'>\n";
  for my $msg (@msg) {
    print "<div class='msg$msg->[0]'>$msg->[1]</div>\n";
  }
  @msg=();
}

sub output_footer {
  print "</td></tr></table>\n";
  print "<div id='kasfoot'>\n";
  print "<a title=\"copyright (c) 2006-2010 by Pieter Wuille\">powered by $VERSION</a></div></body></html>\n";
}

##############################################################################
# top-level code                                                             #
##############################################################################

# load configuration
open CONF,"<kas.conf";
while (<CONF>) {
  chomp;
  next if ($_ =~ /^\s*#/);
  if ($_ =~ /(.*?)\s+(.*)/) {
    $CONF{$1}=$2;
  }
}
close CONF;
foreach my $id (@BOOLS) {
  undef $CONF{$id} if (defined $CONF{$id} && $CONF{$id} && $CONF{$id} eq 'false');
}

# process input
process_input;

# connect
db_connect;

if (defined $ARGV[0] && $ARGV[0] eq 'reset') {
  db_init;
  exit;
}

if (defined $ARGV[0] && $ARGV[0] eq 'recalc') {
  my $level=(defined $ARGV[1] ? $ARGV[1] : 0) || 0;
  perform('db_recalc',level => $level);
  exit;
}

# check for initdb
if ($CONF{initdb}) {
  my $cmd=$0 || $ENV{SCRIPT_NAME};
  push @msg,['warn',"Please initialize the database first, using<br/>\n".
        "  <tt>./$cmd reset</tt>\n".
        "and disable the initdb option in kas.conf before continuing.\n"];
  output_header;
  output_footer;
  exit;
}

# handle authentication
check_auth;

# handle commands
my $command=param('cmd') || "";

# handle forms
if ($command eq 'dona') {
  my $ok=1;
  my $pass1=param('password');
  my $pass2=param('password2');
  my $meth=param('dona_type');
  my $user=param('uname');
  my $email=param('email');
  my $accnr=param('accnr');
  my $fullname=param('fullname');
  if (length($fullname)<4) { $ok=0; push @msg,['warn',"Full name too short (need at least 4 characters)"]; }
  if ($email =~ /[^a-zA-Z0-9._=+@-]/) { $ok=0; push @msg,['warn',"E-mail address contains invalid character"]; }
  if ($email !~ /[a-zA-Z0-9].*@[a-zA-Z0-9].*\.[a-z][a-z]+/) { $ok=0; push @msg,['warn',"E-mail address is invalid"]; }
  if (defined $accnr) { $accnr=parse_iban($accnr); if (!defined $accnr) { $ok=0; push @msg,['warn',"Invalid bank account number"]; } }
  if (defined ($meth) && $meth eq 'pw') {
    if (length($user) < 4) { $ok=0; push @msg,['warn',"Username too short (need at least 4 character)"]; }
    if (length($pass1) < 6) { $ok=0; push @msg,['warn',"Password too short (need at least 6 characters)"]; }
    if ($pass1 ne $pass2) { $ok=0; push @msg,['warn',"Passwords don't match"]; }
  } elsif (defined ($meth) && $meth eq 'ht') {
    if (!defined $ENV{REMOTE_USER}) { $ok=0; push @msg,['warn',"No user logged in"] }
  } else  {
    { $ok=0; push @msg,['warn',"Unknown authentication method '".htmlwrap($meth)."' requested"]; }
  }
  if ($ok) {
    my $rid=generate_sid(160);
    if ($meth eq 'pw') {
      $ok=defined (perform('req_new',rid => $rid, user => $user, fullname => $fullname, accnr => $accnr, email => $email, key => gen_key($pass1)));
    } elsif ($meth eq 'ht') {
      $ok=defined (perform('req_new',rid => $rid, user => $ENV{REMOTE_USER}, fullname => $fullname, accnr => $accnr, email => $email, htname => $ENV{REMOTE_USER}));
    }
    if ($ok) {
      $ok=open(PIPE,"|mail -s 'New account: $title' ".(defined($mailfrom) ? "-a 'From: $mailfrom'" : "")." '$email'");
      if ($ok) { print PIPE "Hello $fullname,\n\na new $title account has been created for you.\nTo activate it, use this link:\n\n  ".url(-base=>1).genurl('activate',$rid)."\n\n-- \nKind regards,\n$title mailer\n"; }
      $ok=(close PIPE) if ($ok);
      push @msg,['succ',"An activation code was mailed to ".htmlwrap($email).". It will remain valid for a week."] if ($ok);
      push @msg,['error',"Could not send e-mail. Try again or contact administrator."] if (!$ok);
    }
  }
  @path=('empty') if ($ok);
}
if ($command eq 'chprof' && defined $auth_username) {
  my $accnr=param('cp_accnr') || undef;
  my $fname=param('cp_fullname');
  my $axept=(param('cp_autoaccept') eq '') ? undef : (param('cp_autoaccept') || 0);
  my $ok=1;
  if (!defined $fname || $fname =~ /\A\s*\Z/) {
    push @msg,['warn',"Full name cannot be empty"];
    $ok=0;
  }
  if (defined $accnr) {
    $accnr=parse_iban($accnr);
    if (!defined $accnr) {
      push @msg,['warn',"Invalid bank account number"];
      $ok=0;
    }
  }
  if ($ok) {
    $ok=defined (perform('prof_edit',fullname => $fname, accnr => $accnr, axept => $axept));
  }
  if ($ok) {
    push @msg,['succ',"Profile updated."];
    @path=();
  }
}
if ($command eq 'chpass' && defined $auth_username) {
  my $sth=db_prepare("SELECT UNAME FROM #USERS WHERE UID=? LIMIT 1");
  $sth->execute($auth_uid);
  my ($username) = $sth->fetchrow_array();
  my $ok=1;
  check_auth($username); # re-check auth based on username/password
  if ($auth_level < $MIN_LEVEL_NOPASSSUDO && index($auth_methods,'|password|')<0) {
    push @msg,['warn',"Invalid old password"];
    $ok=0;
  }
  if (param('newpass1') ne param('newpass2')) {
    push @msg,['warn',"Passwords do not match"];
    $ok=0;
  }
  if (length(param('newpass1'))<6) {
    push @msg,['warn',"New password is too short"];
    $ok=0;
  }
  if ($ok) {
    if (defined (perform('pass_edit',key => gen_key(param('newpass1'))))) {
      push @msg,['succ',"Your password was succesfully changed"];
      @path=();
    }
  }
}
if ($command eq 'dohl' && defined $auth_username) {
  my @ids=split(/,/,param('hl_ids'));
  my @ack=();
  foreach my $id (@ids) {
    my $xx=param("hlx_$id") || "";
    my $x=($xx eq 'd');
    my $am=param("hlv_$id");
    my $o=param("hlo_$id");
    if (($o ne 'r' || ($xx eq 'd' || $xx eq 'a')) && (defined $am) && (defined $o) && ($xx ne $o)) {
      push @ack,[$id,$am,1-$x];
    }
  }
  perform('ack_edit',acks => \@ack);
}
if ($command eq 'addpay' && defined $auth_username) { while(1) {
  my $c_value = calc(param('ap_value'));
  if (!defined $c_value || $c_value<=0) {
    push @msg,["error","Invalid amount for new payment: ".htmlwrap(param('ap_value') || "")];
    last;
  }
  my ($user,$val)=(param('ap_user'),$c_value);
  need_user_list;
  if (!defined $USERS{$user}->{VIS}) {
    push @msg,['warn',"Please select a user"];
    last;
  } else {
    my $ret=perform('pay_new',user => $user,val => $val);
    if (defined $ret) {
      push @msg,['succ',"Payment succesfully added"];
      @path=();
    }
  }
  last;
} }
if ($command eq 'addwant' && defined $auth_username) { while(1) {
  my $gid;
  my $uid;
  my $c_value=calc(param('aw_value'));
  if (!defined $c_value || $c_value==0) {
    push @msg,["error","Invalid price for new item: ".htmlwrap(param('aw_value') || "")];
    last;
  }
  if (param('aw_gtype') eq 'new') {
    my $ret=perform('group_new',name => param('aw_ng_name') || 'group');
    last if (!defined $ret);
    $gid=$ret->{gid};
  } elsif (param('aw_gtype') eq 'user') {
    $uid=param('aw_user');
    need_user_list;
    if (!$USERS{$uid}->{VIS}) {
      push @msg,['warn',"Invalid user for adding item"];
      last;
    }
  } else {
    $gid=param('aw_group');
    need_group_list($gid || 0);
    if (!defined $GROUPS{$gid}) {
      push @msg,['warn',"Invalid group for adding item"];
      last;
    }
  } 
  my $ret=perform('item_new',gid => $gid,uid => $uid,value => $c_value, name => param('aw_name')||'', descr => param('aw_descr')||'');
  if (defined $ret) {
    push @msg,['succ',"Item succesfully added"];
    if (param('aw_gtype') eq 'new') {
      @path=('group',$ret->{gid});
    } else {
      @path=();
    }
  }
  last;
} }
if ($command eq 'addbill' && defined $auth_username) {
  my $ret=perform('bill_new',name => param('ab_name')||"", descr => param('ab_descr')||"");
  if (defined $ret) {
    @path=('bill',$ret->{tid});
  }
}
if ($command eq 'doeg' && defined $auth_username) { while(1) {
  exit if (!$auth_active);
  my $dgid=param('eg_gid');
  need_group_list($dgid || 0);
  if (!defined $GROUPS{$dgid}) {
    push @msg,['warn',"Access denied while editing group"];
    last;
  }
  need_user_list;
  my %ass;
  my $ok=1;
  foreach my $uid (split(/,/,param('eg_uids'))) {
    if (defined($USERS{$uid})) {
      my $par=param("eg_a$uid");
      if (defined $par) {
        my $calc=calc($par);
        if (!defined $calc) {
          push @msg,['warn',"Invalid expression '".htmlwrap($par)."' while editing group."];
          $ok=0;
        }
        $ass{$uid} = [$par,$calc];
      }
    }
  }
  my $max;
  if (defined(param('eg_max'))) {
    my $par=param('eg_max');
    my $calc=calc($par);
    if (!defined $calc) {
      push @msg,['warn',"Invalid expression '".htmlwrap($par)."' in max assignments while editing group."];
      $ok=0;
    }
    $max=[$par,$calc];
  }
  if ($ok) {
    $ok=defined(perform('group_edit',gid => $dgid, max => $max, ass => \%ass, name => param('eg_name') || '-', descr => param('eg_descr') || '', public => param('eg_public')?1:0));
    if ($ok) {
      push @msg,['succ',"Group succesfully modified"];
      @path=();
    }
  }
  last;
} }
if ($command eq 'doep' && defined $auth_username) { while(1) {
  if (param('ep_delete')) {
    my $ok=defined(perform('pay_del',tid => param('ep_id')||(-1)));
    if ($ok) {
      push @msg,['succ',"Payment succesfully deleted"];
      @path=();
    }
    last;
  }
  my $clc=calc(param('ep_value'));
  if (!defined $clc) {
    push @msg,['warn',htmlwrap(param('ep_value') || "") . " is not a valid amount for payment"];
    last;
  }
  my $ok=defined(perform('pay_edit',tid => param('ep_id')||(-1),val => -$clc));
  if ($ok) {
    push @msg,['succ',"Payment succesfully modified"];
    @path=();
  }
  last;
} }
if ($command eq 'doew' && defined $auth_username) { while(1) {
  if (param('ew_delete')) {
    my $ok=defined(perform('item_del',tid => param('ew_id')||(-1)));
    if ($ok) {
      push @msg,['succ',"Item succesfully deleted"];
      @path=();
    }
    last;
  }
  my $clc=calc(param('ew_value'));
  if (!defined $clc) {
    push @msg,['warn',htmlwrap(param('ew_value') || "") . " is not a valid amount for item"];
    last;
  }
  my $ok=defined(perform('item_edit',tid => param('ew_id')||(-1),val => $clc, descr => param('ew_descr')||"", name => param('ew_name')||""));
  if ($ok) {
    push @msg,['succ',"Item succesfully modified"];
    @path=();
  }
  last;
} }
if ($command eq 'doeb' && defined $auth_username) { while(1) {
  if (param('eb_delete')) {
    my $ok=defined(perform('bill_del',tid => param('eb_id')||""));
    if ($ok) {
      push @msg,['succ',"Bill succesfully deleted"];
      @path=();
    }
    last;
  }
  my ($def,$err)=process_bill(param('eb_def') || '',3);
  if (!$err) {
    my $ok=defined(perform('bill_edit',tid => param('eb_id')||(-1),def => $def, descr => param('eb_descr')||"", name => param('eb_name')||""));
    if ($ok) {
      push @msg,['succ',"Bill succesfully modified"];
      @path=();
    }
  }
  last;
} }
if ($command eq 'doev' && defined $auth_username) {
  need_user_list;
  my @vis=();
  for my $uid (split(/,/,param('ev_uids'))) {
    my $par=param("ev_u$uid");
    push @vis,$uid if (defined($par) && $par==1);
  }
  my $ok=defined(perform('vis_edit',vis => \@vis));
  if ($ok) {
    $haveUSERS=0;
    push @msg,['succ',"Connecions succesfully updated"];
    @path=()
  }
}

######################################################################################

if (defined $path[0] && (($path[0] eq 'logout') || $path[0] eq 'activate')) {
  if (defined $session) {
    my $sth=db_prepare("DELETE FROM #SESSION WHERE SID=?");
    $sth->execute($session);
  }
  undef $session;
  undef $auth_username;
  undef $auth_uid;
  undef $auth_fullname;
  undef $auth_level;
  undef $auth_active;
  $auth_methods="";
  @path=('login') if ($path[0] eq 'logout');
}

#####################
### web interface ###
#####################

if (defined $auth_username && !$auth_active) {
  push @msg,['info',"Your account is currently locked. No manipulation of transactions is possible. Contact administrator to have your account unlocked."];
}

my $warned=0;

# redirect if meaningful (path changed) and possible (session to store messages in, or no messages)
if (join('/',@path) ne $oldpath && (defined($session) || $#msg<0)) {
  if ($#msg>=0) {
    my @omsg=@msg;
    my ($ret,@bla)=db_isolate(\&tx_store_msg);
    if ($ret==0) {
      $dbh->disconnect;
      my @cookies=get_cookies;
      print redirect(-url => url(-base=>1).genurl(@path),-status => 303, -cookies => \@cookies);
      exit;
    } else {
      @msg=@omsg;
      log_action("store_msg: failure: ret=$ret ".join(' ',@bla));
    }
  } else {
    $dbh->disconnect;
    my @cookies=get_cookies;
    print redirect(-url => url(-base=>1).genurl(@path),-status => 303, -cookies => \@cookies);
    exit;
  }
}

# handle web interface 
while(1) {
  my $menu=$path[0];
  $menu='default' if (!defined $menu || $menu eq '');
  if ($menu ne 'warn' && !($warned&1)) {
    $warned |= 1;
    my $sth=db_prepare("SELECT EXISTS(SELECT 1 FROM #EF E, #TR T WHERE E.UID=? AND T.TID=E.TID AND ABS(E.AMOUNT-E.SEEN)>=?)");
    $sth->execute($auth_uid,$THRESHOLD);
    my ($ret)=$sth->fetchrow_array;
    if ($ret) {
      push @msg,['info',"You have updated transactions. Please acknowledge them on the <a href=\"".genurl('warn')."\">notifications</a> page."];
    }
    $sth=db_prepare("SELECT EXISTS(SELECT 1 FROM #EF E, #TR T WHERE E.UID=? AND T.AUTHOR=E.UID AND T.TID=E.TID AND EXISTS(SELECT 1 FROM #EF EE WHERE EE.TID=T.TID AND NOT EE.ENABLED))");
    $sth->execute($auth_uid);
    ($ret)=$sth->fetchrow_array;
    if ($ret) {
      push @msg,['info',"Some of your transactions are denied or pending accept. Please check the <a href=\"".genurl('warn')."\">notifications</a> page."];
    }
  }
  if ($menu eq 'default') {
    @path=('error',"No default menu defined");
    @path=('overview') if (defined $auth_username);
    @path=('login') if (!defined $auth_username);
    next;
  } elsif ($menu eq 'info') {
    print "Content-type: text/plain\n\n";
    print "uid: $auth_uid\n";
    print "fullname: $auth_fullname\n";
    print "level: $auth_level\n";
    print "path: ".(join(' ',@path))."\n";
    print "abs url: ".url(-absolute=>1)."\n";
    print "ful url: ".url(-full=>1)."\n";
    print "bas url: ".url(-base=>1)."\n";
    while (my ($key,$val)=each %ENV) {
      print "ENV{$key}='$val'\n";
    }
  } elsif ($menu eq 'group' && defined $auth_username) {
    my $grouptoedit=$path[1];
    need_group_list($grouptoedit);
    need_user_list;
    my $gte=$GROUPS{$grouptoedit};
    if (!defined $gte) {
      push @msg,['warn',"Group does not exist or permission denied"];
      @path=();
      next;
    }
    my $sth=db_prepare("SELECT UID,AMOUNT,FORMULA from #SHARES WHERE GID=?");
    $sth->execute($grouptoedit);
    my %shares;
    my %forms;
    my $sum=0;
    my $sums=0;
    while (my ($k,$v,$f)=$sth->fetchrow_array) {
      $shares{$k}=$v;
      $sums += $v;
      $sum += calc($f);
      $forms{$k}=(defined($f) && $f ne '') ? $f : $v;
    }
    $sth->finish;
    output_header;
    print "<h3>Edit group: ".htmlwrap($gte->{NAME})."</h3>";
    print "<form action='".selfurl."' method='post'>\n";
    print "<table>\n";
    print "<tr class='tblodd'><td>Name:</td><td> <input type='text' name='eg_name' value=".'"'.htmlwrap(param('eg_name') || $gte->{NAME}).'"'." /></td></tr>\n";
    print "<tr class='tbleven'><td>Description:</td><td> <textarea rows='3' cols='60' name='eg_descr'>".htmlwrap(param('eg_descr') || $gte->{DESCR} || "",1)."</textarea></td></tr>\n";
    print "<tr class='tblodd'><td>Max. assignments:</td><td> <input type='text' name='eg_max' value='".(param('eg_max') || $gte->{MAXFORM}||"")."' /></td></tr>\n";
    print "<tr class='tbleven'><td>Old total assignments:</td><td> $sum</td></tr>\n";
    print "<tr class='tblodd'><td>Group created:</td><td> ".substr($gte->{WWHEN},0,16)."</td></tr>\n";
    print "<tr class='tbleven'><td>Reusable:</td><td><input type='checkbox' name='eg_public' value='1' ".((param('eg_public') || $gte->{PUBLIC}) ? " checked='checked'" : "")." /></td></tr>\n";
    print "</table><p>\n";
    print "<input type='hidden' name='eg_uids' value='".join(',',keys %USERS)."' />\n";
    print "<input type='hidden' name='eg_gid' value='$grouptoedit' />\n";
    print "<input type='hidden' name='cmd' value='doeg' />\n";
    print "</p><table width=\"100%\"><col width=\"240\" /><col width=\"*\" /><col width=\"130\" /><tr class='tblhead'><th align=\"left\">Assigned to:</th><th align=\"left\">Amount</th><th align=\"left\">Value</th></tr>\n";
    my $num;
    for (sort { 
      my $s1 = (defined($shares{$a}) && $shares{$a}!=0) ? 1 : 0;
      my $s2 = (defined($shares{$b}) && $shares{$b}!=0) ? 1 : 0;
      return ($s2 <=> $s1) if ($s1 != $s2);
      return (lc($USERS{$a}->{NAME}) cmp lc($USERS{$b}->{NAME})) if (defined $USERS{$a} && defined $USERS{$b});
      return ($a <=> $b);
    } keys %USERS) {
      if (defined $USERS{$_} && $USERS{$_}->{ACTIVE} && ((defined($shares{$_}) && $shares{$_}>0) || $USERS{$_}->{VIS} || $_==$auth_uid)) {
        if (defined($shares{$_}) && $shares{$_}>0 || ($USERS{$_}->{VIS} || $_==$auth_uid)) {
          print "<tr class='".(($num++)%2 ? 'tblodd' : 'tbleven')."'><td>".htmlwrap($USERS{$_}->{NAME})."</td><td><input type='text' name='eg_a$_' value='".htmlwrap(param("eg_a$_") || $forms{$_} || "")."' style=\"width:99.5%\" /></td>".($shares{$_} ? "<td>".sprintf("%.2f",calc($forms{$_}))." (".sprintf("%.2f%%",100*($shares{$_}||0)/($sums||1)).")</td>" : "<td></td>")."</tr>\n";
        }
      } else {
        if (defined($shares{$_}) && $shares{$_}>0) {
          print "<tr class='".(($num++)%2 ? 'tblodd' : 'tbleven')."'><td>Unknown</td><td><input type='hidden' name='eg_a$_' value='".htmlwrap(param("eg_a$_") || $forms{$_} || "")."' style=\"width:99.5%\" />".($forms{$_} || "")."</td>".($shares{$_} ? "<td>".sprintf("%.2f",calc($forms{$_}))." (".sprintf("%.2f%%",100*($shares{$_}||0)/($sums||1)).")</td>" : "<td></td>")."</tr>\n";
        }
      }
    }
    print "</table><p>\n";
    print "<input type='submit' value='Edit' />\n" if ($auth_active);
    print "</p></form>\n";
    print "<a href='$URL'>Go back</a>\n";
    output_footer;
  } elsif ($menu eq 'payment' && defined $auth_username) {
    my $tid=$path[1];
    my $sth=db_prepare("SELECT T.AFU,T.AUTHOR,T.WWHEN,(-I.AMOUNT) FROM #TR T, #ITEM I WHERE T.TID=? AND I.TID=? AND T.NAME IS NULL");
    $sth->execute($tid,$tid);
    my ($pfrom,$pto,$wwhen,$amount) = $sth->fetchrow_array;
    if (!defined $pfrom) {
      push @msg,['warn',"Payment does not exist"];
      @path=();
      next;
    }
    if ($pfrom != $auth_uid && $pto != $auth_uid) {
      push @msg,['warn',"Permission denied for viewing payment"];
      @path=();
      next;
    }
    need_user_list;
    output_header;
    if ($pto eq $auth_uid) {
      print "<h3>Edit payment</h3>\n";
    } else {
      print "<h3>View payment</h3>\n";
    }
    print "<form action='".selfurl."' method='post'>\n";
    print "<table>\n";
    print "<tr class='tblodd'><td>When:</td><td> ".substr($wwhen,0,16)."</td></tr>\n";
    my $pfname=$USERS{$pfrom}->{NAME};
    my $ptname=$USERS{$pto}->{NAME};
    print "<tr class='tbleven'><td>From:</td><td> ".htmlwrap($pfname)."</td></tr>\n";
    print "<tr class='tblodd'><td>To:</td><td> ".htmlwrap($ptname)."</td></tr>\n";
    if ($pto eq $auth_uid) {
      print "<tr class='tbleven'><td>Amount:</td><td> <input type='text' name='ep_value' value='".htmlwrap(param('ep_value') || $amount)."' /></td></tr>\n";
      print "</table><p>\n";
      print "<input type='hidden' name='cmd' value='doep' />\n";
      print "<input type='submit' value='Save' />\n" if ($auth_active);
      print "<input type='submit' name='ep_delete' value='Delete' />\n";
    } else {
      print "<tr class='tbleven'><td>Amount:</td><td>".htmlwrap($amount)."</td></tr>\n";
      print "</table><p>\n";
    }
    print "<input type='hidden' name='ep_id' value='$tid' />\n";
    print "</p></form>\n";
    print "<a href='$URL'>Go back</a>\n";
    $sth->finish;
    output_footer;
    last;
  } elsif ($menu eq 'item' && defined $auth_username) {
    my $tid=$path[1];
    my $sth=db_prepare("SELECT T.AUTHOR,T.AFG,T.AFU,I.AMOUNT,T.WWHEN,T.NAME,T.DESCR FROM #TR T, #ITEM I WHERE T.TID=? AND I.TID=?");
    $sth->execute($tid,$tid);
    my ($wanter,$wantedg,$wantedu,$amount,$wwhen,$name,$descr)=$sth->fetchrow_array;
    if (!defined $wanter) {
      push @msg,['warn',"Item does not exist"];
      @path=();
      next;
    }
    need_user_list;
    need_group_list($wantedg) if (defined $wantedg);
    if ($auth_uid!=$wanter && defined $wantedg && !defined $GROUPS{$wantedg}) {
      push @msg,['warn',"Permission denied for viewing item"];
      @path=();
      next;
    }
    if ($auth_uid!=$wanter && defined $wantedu && !defined $USERS{$wantedu}) {
      push @msg,['warn',"Permission denied for viewing item"];
      @path=();
      next;
    }
    output_header;
    if ($wanter eq $auth_uid) {
      print "<h3>Edit item</h3>\n";
    } else {
      print "<h3>View item</h3>\n";
    }
    print "<form action='".selfurl."' method='post'>\n";
    print "<table>\n";
    print "<tr class='tblodd'><td>When:</td><td>".substr($wwhen,0,16)."</td></tr>\n";
    print "<tr class='tbleven'><td>Paid by:</td><td> ".htmlwrap($USERS{$wanter}->{NAME})."</td></tr>\n";
    print "<tr class='tblodd'><td>Paid for:</td><td> <a href='".genurl('group',$wantedg)."'>".htmlwrap($GROUPS{$wantedg}->{DNAME})."</a></td></tr>\n" if (defined $wantedg);
    print "<tr class='tblodd'><td>Paid for:</td><td> ".htmlwrap($USERS{$wantedu}->{NAME})."</td></tr>\n" if (defined $wantedu);
    if ($wanter eq $auth_uid) {
      print "<tr class='tbleven'><td>Name:</td><td> <input type='text' name='ew_name' value='".htmlwrap(param('ew_name') || $name)."' /></td></tr>\n";
      print "<tr class='tblodd'><td>Description:</td><td><textarea rows='3' cols='60' name='ew_descr'>".htmlwrap(param('ew_descr') || $descr,1)."</textarea></td></tr>\n";
      print "<tr class='tbleven'><td>Amount:</td><td> <input type='text' name='ew_value' value='$amount' /></td></tr>\n";
      print "</table><p>\n";
      print "<input type='hidden' name='cmd' value='doew' />\n";
      print "<input type='submit' value='Update' />" if ($auth_active);
      print "<input type='submit' name='ew_delete' value='Delete' />";
    } else {
      print "<tr class='tbleven'><td>Name:</td><td> ".htmlwrap($name)."</td></tr>\n";
      print "<tr class='tblodd'><td>Description:</td><td> ".htmlwrap($descr)."</td></tr>\n";
      print "<tr class='tbleven'><td>Amount:</td><td> $amount</td></tr>\n";
      print "</table><p>\n";
    }
    print "<input type='hidden' name='ew_id' value='$tid' />\n";
    print "</p></form>";
    print "<a href='$URL'>Go back</a>\n";
    $sth->finish;
    output_footer;
    last;
  } elsif ($menu eq 'bill' && defined $auth_username) {
    my $tid=$path[1];
    my $sth=db_prepare("SELECT T.AUTHOR,B.DEFINITION,T.NAME,T.DESCR,T.WWHEN FROM #TR T, #BILL B WHERE T.TID=? AND B.TID=?");
    $sth->execute($tid,$tid);
    my ($definer,$definition,$name,$descr,$wwhen)=$sth->fetchrow_array;
    if (!defined $definer) {
      push @msg,['warn',"Bill does not exist"];
      @path=();
      next;
    }
    need_user_list;
    $sth=db_prepare("SELECT EXISTS(SELECT 1 FROM #EF WHERE TID=? AND UID=?)");
    $sth->execute($tid,$auth_uid);
    my ($cnt)=$sth->fetchrow_array;
    if (!$cnt) {
      push @msg,['warn',"Permission denied for viewing bill"];
      @path=();
      next;
    }
    output_header;
    if ($definer == $auth_uid) {
      print "<h3>Edit bill</h3>\n";
    } else {
      print "<h3>View bill</h3>\n";
    }
    print "To learn more about bills, see the <a href='".genurl('help','bill')."'>help</a> pages\n";
    print "<form action='".selfurl."' method='post'><p>\n";
    print "<input type='hidden' name='eb_id' value='$tid' />\n";
    print "</p><table>\n";
    print "<tr class='tblodd'><td>When:</td><td>".substr($wwhen,0,16)."</td></tr>\n";
    print "<tr class='tbleven'><td>Paid by:</td><td> ".htmlwrap($USERS{$definer}->{NAME})."</td></tr>\n";
    my ($ndef,$err,$tot,$cont,@eff);
    my $odef=param('eb_def');
    if (defined $odef) {
      $ndef=$odef;
      (undef,$err,$tot,$cont,@eff) = process_bill($odef,0);
      $name=param('eb_name') || "";
      $descr=param('eb_descr') || "";
    } else {
      ($ndef,$err,$tot,$cont,@eff) = process_bill($definition,$definer==$auth_uid ? 2 : 1);
    }
    print "<tr class='tblodd'><td>Name:</td><td> <input type='text' name='eb_name' value='".htmlwrap($name)."' /></td></tr>\n";
    print "<tr class='tbleven'><td>Description:</td><td><textarea rows='3' cols='60' name='eb_descr'>".htmlwrap($descr,1)."</textarea></td></tr>\n";
    print "<tr class='tblodd'><td>Total amount:</td><td>".sprintf("$UNIT%.2f",$tot)."</td></tr>\n";
    print "<tr class='tbleven'><td>Contributions:</td><td>".sprintf("$UNIT%.2f",$cont)."</td></tr>\n";
    print "<tr class='tblodd'><td>Bill:</td><td><textarea rows='20' cols='60' name='eb_def'>".htmlwrap($ndef,1)."</textarea></td></tr>\n";
    print "<tr class='tbleven'><td>Personal detail:</td><td><ul>";
    foreach my $eff (@eff) {
      my ($uid,$num,$den,$amount,$name)=@{$eff};
      if ($uid==$auth_uid && $num!=0 && $amount != 0) {
        print ("<li>".(sprintf("$UNIT%.2f",$amount*$num/$den))." [");
        if ($num>=1 && $den==1) {
          print "Contribution";
        } else {
          if ($num<-1 && $den==1) {
            printf ((-$num)."x $UNIT%.2f ",$amount);
          } elsif ($num<0 && $den>1) {
            printf ((-$num)."/".($den)." of $UNIT%.2f ",$amount);
          }
          if (defined $name) {
            print htmlwrap($name);
          } else {
            print "item";
          }
        }
        print "]</li>\n";
      }
    }
    print "</ul></td></tr>\n";
    if ($definer eq $auth_uid) {
      print "</table><p>\n";
      print "<input type='hidden' name='cmd' value='doeb' />\n";
      print "<input type='submit' value='Update' />" if ($auth_active);
      print "<input type='submit' name='eb_delete' value='Delete' />";
      print "</p>\n";
    } else {
      print "</table>\n";
    }
    print "</form><br/>";
    print "<a href='$URL'>Go back</a>\n";
    $sth->finish;
    output_footer;
    last;
  } elsif ($menu eq 'connections' && defined $auth_username) {
    need_user_list(1);
    output_header;
    print "<h3>Edit visible people</h3>\n";
    print "<form action='".selfurl."' method='post'>\n";
    print "<p><input type='hidden' name='cmd' value='doev' />\n";
    my %au;
    for (sort {
      my $x=(defined($a->{VIS}) ? 0 : 1) <=> (defined($b->{VIS}) ? 0 : 1);
      return $x if ($x != 0);
      return lc($a->{NAME}) cmp lc($b->{NAME});
    } (values %USERS)) {
      if ($_->{UID}!=$auth_uid && $_->{ACTIVE}) {
        print "<input type='checkbox' name='ev_u$_->{UID}' value='1' ".(defined($_->{VIS}) ? "checked='checked'" : "")."/> ".$_->{NAME}."<br/>\n";
        $au{$_->{UID}}=1;
      }
    }
    print "<input type='hidden' name='ev_uids' value='".join(',',sort keys %au)."' />\n";
    print "<input type='submit' value='Submit' /></p>\n";
    print "</form>\n";
    output_footer;
  } elsif ($menu eq 'rss') { # TODO: up-to-date brengen
    need_user_list;
    print "Content-Type: text/xml; charset=\"utf-8\"\n\n";
    print "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n";
    print "<rss version=\"2.0\" xmlns:dc=\"http://purl.org/dc/elements/1.1/\">\n";
    print "  <channel>\n";
    print "    <title>$title (for ".htmlwrap($auth_fullname).")</title>\n";
    print "    <link>".genurl('rss')."</link>\n";
    print "    <description>$title - transactions for ".htmlwrap($auth_fullname)."</description>\n";
    if (defined $auth_username) {
      my $sth=db_prepare("SELECT AMOUNT,DESCR,WWHEN,TYP,ID FROM #LIST WHERE UID=? ORDER BY WWHEN DESC");
      $sth->execute($auth_uid);
      my $count=0;
      while ((my ($amount,$descr,$wwhen,$type,$id) = $sth->fetchrow_array) && $count<30) {
        if ($type eq 'p' || $type eq 'w') {
          if ($count==0) {
            print "    <item>\n";
            print "      <title>Total ".htmlwrap($auth_fullname).": ".sprintf("%.2f",$USERS{$auth_uid}->{TOTAL})."</title>\n";
            print "      <link>".genurl('rss')."</link>\n";
            print "      <pubDate>$wwhen</pubDate>\n";
            print "    </item>\n";
            print "    <lastBuildDate>$wwhen</lastBuildDate>\n";
          }
          print "    <item>\n";
          print "      <title>".sprintf("%.2f",$amount)." : ".$descr."</title>\n";
          print "      <link>".($type eq 'p' ? genurl('payment',$id) : ($type eq 'w' ? genurl('item',$id) : "$URL"))."</link>\n";
          print "      <pubDate>".($wwhen||"never")."</pubDate>\n";
          print "    </item>\n";
          $count++;
        }
      }
      $sth->finish;
    }
    print "   </channel>\n";
    print "</rss>\n";
  } elsif ($menu eq 'activate') {
    my $code=$path[1];
    my $ok=defined(perform('req_proc',code => $code));
    if ($ok) {
      push @msg,['succ',"Creation succesful. You can log in now."];
      @path=();
      next;
    } else {
      push @msg,['error',"Could not create account. Retry of inform administrator."];
      output_header;
      output_footer;
    }
  } elsif ($menu eq 'overview' && defined $auth_username) {
    need_user_list;
    if ((scalar (grep { ($USERS{$_}->{UID} ne $auth_uid) && (defined $USERS{$_}->{VIS}) && ($USERS{$_}->{ACTIVE})} (keys %USERS)))==0) {
      push @msg,['info',"You do not have anyone visible. Go to <a href='".genurl('connections')."'>connections</a> to add some people."];
    }
    output_header;
    show_totals;
    print "<hr/>\n";
    if (show_unassigned) {
      print "<hr/>\n";
    }
    show_history(0);
    output_footer;
  } elsif ($menu eq 'warn') {
    output_header;
    show_warn;
    print "<hr/>\n";
    show_denied;
    output_footer;
  } elsif ($menu eq 'history') {
    output_header;
    show_history(1);
    output_footer;
  } elsif ($menu eq 'add') {
    output_header;
    show_form_add_pay;
    print "<hr/>\n";
    show_form_add_item;
    print "<hr/>\n";
    show_form_add_bill;
    output_footer;
  } elsif ($menu eq 'settings') {
    output_header;
    show_change_settings;
    print "<br/>\n";
    show_change_password;
    output_footer;
  } elsif ($menu eq 'login') {
    my $alreadyht=0;
    if (defined $ENV{REMOTE_USER} && $ENV{REMOTE_USER} ne '') {
      my $sth=db_prepare("SELECT EXISTS(SELECT 1 FROM #HTAUTH WHERE HTNAME=?)");
      $sth->execute($ENV{REMOTE_USER});
      my ($cnt)=$sth->fetchrow_array;
      if ($cnt) {
        push @msg,['info',"It seems you are already authenticated as ".htmlwrap($ENV{REMOTE_USER}).". Click <a href='$URL'>here</a> to log in automatically."];
        $alreadyht=1;
      }
    }
    output_header;
    print "<h3>Log in:</h3>";
    print "<form action='".selfurl."' method='post'>";
    print "<table>";
    print "<tr class='tblodd'><td>Username:</td><td> <input type='text' name='username' value='".htmlwrap(param('username') || '')."' /></td></tr>";
    print "<tr class='tbleven'><td>Password:</td><td> <input type='password' name='password' /></td></tr>";
    print "</table>\n";
    print "<p><input type='submit' value='Log in' /></p>";
    print "</form>\n";
    print "<h3>Create new account:</h3>\n";
    print "<form action='".selfurl."' method='post'>";
    print "<table>";
    print "<tr class='tblodd'><td>Full name:</td><td> <input type='text' name='fullname' /></td><td></td></tr>\n";
    print "<tr class='tbleven'><td>E-mail address:</td><td> <input type='text' name='email' /></td><td>(must be unique)</td></tr>\n";
    print "<tr class='tblodd'><td>Bank account number:</td><td> <input type='text' name='accnr' /> </td><td>(optional)</td></tr>\n";
    if (!$alreadyht && defined $ENV{REMOTE_USER}) {
      print "<tr class='tbleven'><td>Username:</td><td> $ENV{REMOTE_USER}</td><td></td></tr>\n";
#      print "<li>Login method: <br/><ul>\n";
#      print "<li><input type='radio' name='dona_type' value='ht' checked='checked'/> Automatic login: $ENV{REMOTE_USER} </li>\n";
#      print "<li><input type='radio' name='dona_type' value='pw' /> Username/password: <ul><li>Username: <input type='text' name='username' value='".htmlwrap(param('username') || $ENV{REMOTE_USER} || '')."'/></li>\n<li>Password: <input type='password' name='password' /></li>\n<li>Repeat password: <input type='password' name='password2' /></li></li></ul>\n";
#      print "</ul></li>\n";
      print "</table><p>\n";
      print "<input type='hidden' name='dona_type' value='ht' />\n";
    } else {
      print "<tr class='tbleven'><td>Username:</td><td> <input type='text' name='uname' value='".htmlwrap(param('username') || '')."'/></td><td>(must be unique)</td></tr>\n";
      print "<tr class='tblodd'><td>Password:</td><td> <input type='password' name='password' /></td><td>(6 characters minimum)</td></tr>\n";
      print "<tr class='tbleven'><td>Repeat password:</td><td> <input type='password' name='password2' /></td><td></td></tr>\n";
      print "</table><p>\n";
      print "<input type='hidden' name='dona_type' value='pw' />\n";
    }
    print "<input type='hidden' name='cmd' value='dona' />\n";
    print "<input type='submit' value='Request account' /></p>\n";
    print "</form>\n";
    output_footer;
  } elsif ($menu eq 'empty') {
    output_header;
    output_footer;
  } elsif ($menu eq 'error') {
    for my $err (@path[1..$#path]) {
      push @msg,['error',htmlwrap($err)];
    }
    output_header;
    output_footer;
  } elsif ($menu eq 'information') {
    for my $err (@path[1..$#path]) {
      push @msg,['info',htmlwrap($err)];
    }
    output_header;
    output_footer;
  } elsif ($menu eq 'warning') {
    for my $err (@path[1..$#path]) {
      push @msg,['warn',htmlwrap($err)];
    }
    output_header;
    output_footer;
  } elsif ($menu eq 'succes') {
    for my $err (@path[1..$#path]) {
      push @msg,['succ',htmlwrap($err)];
    }
    output_header;
    output_footer;
  } elsif ($menu eq 'help') {
    my @help=('help',@path[1..$#path]);
    foreach my $help (@help) { $help =~ s/[^a-zA-Z0-9]//g; }
    while(1) {
      my $str="doc/".join('-',@help).".shtml";
      if (! -f $str) {
        pop @help;
      } else {
        open HELPFILE,"<$str";
        output_header;
        print "<div class='helpnav'>";
        for (my $i=0; $i<=$#help; $i++) {
          print " / " if ($i);
          print "<a href=\"".genurl(@help[0..$i])."\">".$help[$i]."</a>";
        }
        print "</div>\n";
        foreach my $text (<HELPFILE>) {
          $text =~ s/\$URL\((.*?)\)/pathurl($1)/eg;
          $text =~ s/\$FULLNAME/htmlwrap(defined $auth_uid ? $auth_fullname : "Your Name")/eg;
          $text =~ s/\$UNIT/$UNIT/g;
          $text =~ s/\$TITLE/htmlwrap($title)/g;
          print $text;
        }
        close HELPFILE;
        output_footer;
        last;
      }
    }
  } else {
    push @msg,['warn',"Unknown or inaccessible menu: ".htmlwrap($menu)];
    output_header;
    output_footer;
  }
  last;
}

# disconnect
$dbh->disconnect;
