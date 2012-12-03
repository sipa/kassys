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

# version
my $SYSTEM="Kassys";
my $MAJOR=0;
my $MINOR=9;
my $REVISION=196;
my $VERSION="$SYSTEM v$MAJOR.$MINOR.$REVISION";
# REV=$(svn log kas.cgi | egrep '^r[0-9]+ ' | wc -l); sed -re "s/ \\\$REVISION=[0-9]+;/ \$REVISION=$REV;/" -i kas.cgi

# global constants
my $DENOM=18018000;        # 18018000 = kgv(2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,1000)
my $PCT=1.03;              # (annual) interest ratio for annuity corrections
my $SEC_PER_YEAR=31556952; # average number of seconds in gregorian year
my $THRESHOLD=0.005;       # differences below this many monetary units are ignored
my $SESSION_TIME=30;       # session lifetime, in minutes
my $UNIT="&#8364; ";       # monetary unit

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

my ($URL,@path,$DIR,$SCRIPT);

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
#  if ($CONF{pathinfo}) {
    $SCRIPT=filepart($ENV{SCRIPT_NAME});
#  }
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
    print LOG "[".time.(defined $auth_uid ? " $auth_uid($auth_fullname)" : "")."] $_\n";
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

##############################################################################
# database functions                                                         #
##############################################################################

# establish database connection
sub connect_db {
  my $dbname=$CONF{dbname};
  my $host=$CONF{dbhost} || "localhost";
  my $dbusername=$CONF{dbuser};
  my $dbpassword=$CONF{dbpass};
  $dbh = DBI->connect("dbi:Pg:dbname=$dbname;host=$host", $dbusername, $dbpassword,{AutoCommit => 1,RaiseError => 0}) or die "Unable to connect: $DBI::errstr\n";
  $prefix=defined($CONF{dbprefix}) ? "$CONF{dbprefix}_" : "";
  $title=$CONF{title} || $VERSION;
  $htmltitle=$CONF{htmltitle} || $title;
  $mailfrom=$CONF{mailfrom};
}

sub reset_db {
  die "Resetting database requires 'initdb true' in kas.conf" unless ($CONF{initdb});

  $dbh->do("DROP INDEX ${prefix}IDX_SHARES_GID CASCADE");
  $dbh->do("DROP INDEX ${prefix}IDX_TR_WWHEN CASCADE");
  $dbh->do("DROP INDEX ${prefix}IDX_EF_TID CASCADE");
  $dbh->do("DROP INDEX ${prefix}IDX_EF_UID CASCADE");
  $dbh->do("DROP INDEX ${prefix}IDX_VISIBLE_SEER CASCADE");
  $dbh->do("DROP INDEX ${prefix}IDX_EDGEINFO_ETYP_EFROM CASCADE");
  $dbh->do("DROP TABLE ${prefix}SESSION CASCADE");
  $dbh->do("DROP TABLE ${prefix}VISIBLE CASCADE");
  $dbh->do("DROP TABLE ${prefix}EDGEINFO CASCADE");
  $dbh->do("DROP TABLE ${prefix}BILL CASCADE");
  $dbh->do("DROP TABLE ${prefix}ITEM CASCADE");
  $dbh->do("DROP TABLE ${prefix}EF CASCADE");
  $dbh->do("DROP TABLE ${prefix}TR CASCADE");
  $dbh->do("DROP TABLE ${prefix}SHARES CASCADE");
  $dbh->do("DROP TABLE ${prefix}GROUPS CASCADE");
  $dbh->do("DROP TABLE ${prefix}HTAUTH CASCADE");
  $dbh->do("DROP TABLE ${prefix}PWAUTH CASCADE");
  $dbh->do("DROP TABLE ${prefix}USERREQ CASCADE");
  $dbh->do("DROP TABLE ${prefix}USERS CASCADE");
  $dbh->do("DROP SEQUENCE ${prefix}NTR CASCADE");
  $dbh->do("DROP SEQUENCE ${prefix}NGROUPS CASCADE");
  $dbh->do("DROP SEQUENCE ${prefix}NUSERS CASCADE");

  $dbh->do("CREATE SEQUENCE ${prefix}NUSERS");
  $dbh->do("CREATE SEQUENCE ${prefix}NGROUPS");
  $dbh->do("CREATE SEQUENCE ${prefix}NTR");
  $dbh->do("CREATE TABLE ${prefix}USERS (".   # list of active users
             "UID INT4 PRIMARY KEY NOT NULL DEFAULT nextval('${prefix}NUSERS'), ".  # unique user id
             "UNAME VARCHAR(63) NOT NULL, ".  # unique username
             "FULLNAME TEXT NOT NULL, ".      # full name
             "ACCNR VARCHAR(40), ".           # bank account number
             "ACTIVE BOOLEAN NOT NULL DEFAULT FALSE, ". # active user?
             "EMAIL VARCHAR(255) NOT NULL, ". # email address
             "TOTALSUM NUMERIC(20,10) NOT NULL DEFAULT 0, ".  # sum of all included (counted) transactions for this user
             "TOTALPCT NUMERIC(20,10) NOT NULL DEFAULT 0, ".  # same, but annuity-corrected for the timestamp represented by 'created' field
             "CREATED TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP, ". # when account was created (not requested)
             "I18N VARCHAR(3) NOT NULL DEFAULT 'en', ". # language
             "AUTOACCEPT NUMERIC(12,4) NOT NULL DEFAULT 50, ". # automatically accept charges up to this amount
             "NICKNAME VARCHAR(40) NULL DEFAULT NULL, ". # nickname
             "UNIQUE (UNAME), ".
             "UNIQUE (EMAIL)".
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}USERREQ (". # list of user-account requests
             "RID VARCHAR(63) PRIMARY KEY NOT NULL, ". # unique request ID
             "EXPIRE TIMESTAMP NOT NULL DEFAULT (CURRENT_TIMESTAMP + interval '7 days'), ". # when does request expire
             "UNAME VARCHAR(63) NULL, ".      # requested username
             "UID INT4 NULL REFERENCES ${prefix}USERS, ". # user to edit (when changing password)
             "FULLNAME TEXT NULL, ".          # provided fullname
             "ACCNR VARCHAR(40), ".           # provided account number
             "EMAIL VARCHAR(255) NULL, ".     # provided email adres
             "HTNAME VARCHAR(64) NULL, ".     # http-auth username during account request
             "PWKEY VARCHAR(255) NULL, ".     # requested password (encoded using gen_key)
             "LEVEL INT4 NOT NULL DEFAULT 1". # requested permission level (TODO: check this when creating account...)
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}PWAUTH (".  # password-based authentication list
             "UID INT4 NOT NULL REFERENCES ${prefix}USERS, ". # user-id this password is valid for
             "KEY VARCHAR(255) NOT NULL, ".   # password stored as a key (using gen_key)
             "LEVEL INT4 NOT NULL DEFAULT 1, ". # permission level
             "UNIQUE (UID)".
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}HTAUTH (".  # http-auth based authentication list
             "UID INT4 NOT NULL REFERENCES ${prefix}USERS, ". # user-id this http-auth is valid for
             "HTNAME VARCHAR(64) PRIMARY KEY NOT NULL, ". # what name to use
             "LEVEL INT4 NOT NULL DEFAULT 1, ". # permission level
             "UNIQUE (UID)".
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}GROUPS (".
             "GID INT4 PRIMARY KEY NOT NULL DEFAULT nextval('${prefix}NGROUPS'), ". # unique group identifier
             "DEFINER INT4 NOT NULL REFERENCES ${prefix}USERS, ". # who created the group
             "NAME VARCHAR(40) NOT NULL, ". # name of the group
             "DESCR TEXT NULL, ". # description of the group
             "ISPUBLIC BOOL NOT NULL DEFAULT FALSE, ". # whether group is public
             "MAX INT4 NOT NULL DEFAULT 0, ".          # maximum number of shares (if larger than total: unassigned)
             "MAXFORM TEXT, ".        # formula for maximum number of shares
             "WWHEN TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP, ". # creation time
             "UNIQUE (NAME,WWHEN)".
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}SHARES (".
             "GID INT4 REFERENCES ${prefix}GROUPS NOT NULL, ". # group this is a share of
             "UID INT4 REFERENCES ${prefix}USERS NOT NULL, ".  # user that is share of group
             "AMOUNT INT4 NOT NULL CHECK (amount>0), ".        # how many shares
             "FORMULA TEXT, ". # formula for shares
             "UNIQUE (GID,UID)".
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}TR (". # transactions (payments, items, bills, ...)
             "TID INT8 PRIMARY KEY NOT NULL DEFAULT nextval('${prefix}NTR'), ". # transaction id
             "TYP CHAR NOT NULL, ". # what type ('i'=item/payment, 'b'=bill)
             "NAME VARCHAR(40) NULL, ". # name of item/bill (nameless item against a user = payment)
             "DESCR TEXT NULL, ". # extra description
             "AUTHOR INT4 NOT NULL REFERENCES ${prefix}USERS, ". # who created the transaction
             "ACTIVE BOOL NOT NULL DEFAULT TRUE, ". # whether the transaction should be counted
             "COUNTED BOOL NOT NULL DEFAULT FALSE, ". # whether the transaction is counted in total
             "WWHEN TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP, ". # creation time of transaction
             "AFG INT4 NULL REFERENCES ${prefix}GROUPS, ". # affected user
             "AFU INT4 NULL REFERENCES ${prefix}USERS".    # affected group
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}EF (". # effect of a transaction
             "TID INT8 NOT NULL REFERENCES ${prefix}TR, ". # transaction this is an effect of
             "UID INT4 NOT NULL REFERENCES ${prefix}USERS, ". # user that is affected
             "AMOUNT NUMERIC(18,10) NOT NULL DEFAULT 0, ". # for which amount
             "SEEN NUMERIC(18,10) NOT NULL DEFAULT 0, ".   # which amount was (either positively or negatively) acknowledged by user
             "ACCEPT BOOL NULL, ". # null=not seen, true=accepted, false=declined
             "PRIMARY KEY (TID,UID) ".
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}ITEM (".
             "TID INT8 NOT NULL REFERENCES ${prefix}TR, ".
             "AMOUNT NUMERIC(12,4), ".
             "UNIQUE (TID) ".
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}BILL (".
             "TID INT8 NOT NULL REFERENCES ${prefix}TR, ".
             "DEFINITION TEXT NOT NULL, ".
             "UNIQUE (TID) ".
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}EDGEINFO (".
             "EFROM INT4 REFERENCES ${prefix}USERS NOT NULL, ".
             "ETO INT4 REFERENCES ${prefix}USERS NOT NULL, ".
             "ETYP CHAR NOT NULL, ".
             "TOTALSUM NUMERIC(20,10) NOT NULL DEFAULT 0, ".
             "TOTALPCT NUMERIC(20,10) NOT NULL DEFAULT 0, ".
             "CREATED TIMESTAMP NOT NULL DEFAULT CURRENT_TIMESTAMP, ".
             "PRIMARY KEY (EFROM,ETO,ETYP)".
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}VISIBLE (".
             "SEER INT4 REFERENCES ${prefix}USERS NOT NULL, ".
             "SEEN INT4 REFERENCES ${prefix}USERS NOT NULL, ".
             "LEVEL DOUBLE PRECISION NOT NULL DEFAULT 1, ".
             "PRIMARY KEY (SEER,SEEN) ".
           ") WITHOUT OIDS");
  $dbh->do("CREATE TABLE ${prefix}SESSION (".
             "SID VARCHAR(86) PRIMARY KEY NOT NULL, ".
             "UID INT4 REFERENCES ${prefix}USERS NOT NULL, ".
             "EXPIRE TIMESTAMP NOT NULL, ".
             "LEVEL INT4 NOT NULL ".
           ") WITHOUT OIDS");
  $dbh->do(
    "CREATE VIEW ${prefix}USERLIST AS ".
      "SELECT U.UID AS UID, U.ACTIVE, U.FULLNAME AS NAME, U.TOTALSUM as TOTAL, U.TOTALPCT*POW($PCT,EXTRACT(EPOCH FROM (CURRENT_TIMESTAMP-U.CREATED))/$SEC_PER_YEAR)-U.TOTALSUM AS EXTRA, U.ACCNR AS ACCNR ".
        "FROM ${prefix}USERS AS U"
  );
  $dbh->do("CREATE INDEX ${prefix}IDX_SHARES_GID ON ${prefix}SHARES (GID)");
  $dbh->do("CREATE INDEX ${prefix}IDX_TR_WWHEN ON ${prefix}TR (WWHEN)");
  $dbh->do("CREATE INDEX ${prefix}IDX_EF_TID ON ${prefix}EF (TID)");
  $dbh->do("CREATE INDEX ${prefix}IDX_EF_UID ON ${prefix}EF (UID)");
  $dbh->do("CREATE INDEX ${prefix}IDX_VISIBLE_SEER ON ${prefix}VISIBLE (SEER)");
  $dbh->do("CREATE INDEX ${prefix}IDX_EDGEINFO_ETYP_EFROM ON ${prefix}EDGEINFO (ETYP,EFROM)");
}

# initialize database
sub init_db {
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
  reset_db;
  print STDERR "Start creating entries...\n";
  my $sth=$dbh->prepare("INSERT INTO ${prefix}USERS (uid,uname,fullname,email) VALUES (-1,'admin','Administrator',?)");
  $sth->execute($email);
  $dbh->do("INSERT INTO ${prefix}PWAUTH (uid,key,level) VALUES (-1,'".gen_key($pass1)."',100)");
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
    $dbh->begin_work;
    my $sth2=$dbh->prepare("DELETE FROM ${prefix}SESSION WHERE EXPIRE<CURRENT_TIMESTAMP");
    $sth2->execute;
    $dbh->commit;
    my $sth=$dbh->prepare("SELECT S.UID,S.LEVEL,U.FULLNAME,U.UNAME,U.ACTIVE,U.AUTOACCEPT FROM ${prefix}SESSION AS S, ${prefix}USERS AS U WHERE S.SID=? AND S.UID=U.UID");
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
    } else {
      undef $session; # no valid $session - clear it to recreate it later
    }
  }
  # try http auth
  if ($auth_level<0 && defined $ENV{REMOTE_USER}) {
    my $sth4=$dbh->prepare("SELECT A.UID,A.LEVEL,U.FULLNAME,U.UNAME,U.ACTIVE,U.AUTOACCEPT FROM ${prefix}HTAUTH AS A, ${prefix}USERS AS U WHERE A.HTNAME=? AND U.UID=A.UID");
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
  if ($auth_level<0 && (defined $username && $username ne '' && ($auth_level>=$MIN_LEVEL_NOPASSSUDO || defined $password))) {
    my $sth3=$dbh->prepare("SELECT A.UID,A.KEY,A.LEVEL,U.FULLNAME,U.UNAME,U.ACTIVE,U.AUTOACCEPT FROM ${prefix}PWAUTH AS A, ${prefix}USERS AS U WHERE U.UNAME=? AND U.UID=A.UID");
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
        push @msg,['error',"Password mismatch"] if (!defined $auth_username);
      }
    }
    push @msg,['error',"User not found"] if ($cnt==0 && !defined $auth_username);
    $sth3->finish;
  }
  # update session cache
  if ($auth_level>0) {
    $dbh->begin_work;
    my $sth5;
    if (!defined $session) { # no valid session already in session table - create new one
      $session=generate_sid(256);
      $sth5=$dbh->prepare("INSERT INTO ${prefix}SESSION (UID,LEVEL,SID,EXPIRE) VALUES (?,?,?,CURRENT_TIMESTAMP + INTERVAL '${SESSION_TIME} minutes')");
    } else { # update old session entry
      $sth5=$dbh->prepare("UPDATE ${prefix}SESSION SET UID=?, LEVEL=?, EXPIRE=CURRENT_TIMESTAMP + INTERVAL '${SESSION_TIME} minutes' WHERE SID=?");
    }
    $sth5->execute($auth_uid,$auth_level,$session);
    trycommit(0);
  }
}

# change a password
sub set_password {
  my ($key,$uid,$level,$lock)=@_;
  $uid=$auth_uid if (!defined $uid);
  $level=1 if (!defined $level);
  return 0 if (!defined $uid);
  $dbh->begin_work if (!defined $lock);
  my $sth=$dbh->prepare("DELETE FROM ${prefix}PWAUTH WHERE UID=?");
  $sth->execute($uid);
  $sth=$dbh->prepare("INSERT INTO ${prefix}PWAUTH (KEY,UID,LEVEL) VALUES (?,?,?)");
  $sth->execute($key,$uid,$level);
  $sth->finish;
  trycommit(0) if (!defined $lock);
  return 1;
}

sub set_htlogin {
  my ($htname,$uid,$level,$lock)=@_;
  $uid=$auth_uid if (!defined $uid);
  return 0 if (!defined $uid);
  $dbh->begin_work if (!defined $lock);
  my $sth=$dbh->prepare("DELETE FROM ${prefix}HTAUTH WHERE HTNAME=?");
  $sth->execute($htname);
  $sth=$dbh->prepare("INSERT INTO ${prefix}HTAUTH (HTNAME,UID,LEVEL) VALUES (?,?,?)");
  $sth->execute($htname,$uid,$level);
  $sth->finish;
  trycommit(0) if (!defined $lock);
  return 1;
}

# create a user
sub create_user {
  my ($user,$fullname,$email,$lock)=@_;
  $dbh->begin_work if (!defined $lock);
  my $sth=$dbh->prepare("SELECT nextval('${prefix}NUSERS')");
  $sth->execute;
  my ($nuid)=$sth->fetchrow_array;
  $sth->finish;
  $sth=$dbh->prepare("INSERT INTO ${prefix}USERS (UID,UNAME,FULLNAME,EMAIL,ACTIVE) VALUES (?,?,?,?,?)");
  my $ret=$sth->execute($nuid,$user,normalize_name($fullname),$email,0);
  if (defined $ret && $ret>0) {
    $sth=$dbh->prepare("DELETE FROM ${prefix}USERREQ WHERE UNAME=?");
    $sth->execute($user);
    $sth->finish;
    if (!defined $lock) {
      return $nuid if ($dbh->commit);
      return undef;
    }
    return $nuid;
  } else {
    push @msg,['warn',"Unable to create user. Username or e-mail address may have already been taken."];
    $dbh->rollback if (!defined $lock);
    return undef;
  }
}

# include/exclude transaction from total view
sub count_transaction {
  my ($tid,$count,$locked) = @_;
  do {
    $dbh->begin_work if (!defined $locked);
    my $sth=$dbh->prepare("SELECT COUNT(*) FROM ${prefix}TR T WHERE TID=? AND COUNTED=TRUE"); # check whether this transaction is already included in totals
    $sth->execute($tid);
    my ($cnt)=($sth->fetchrow_array)||0;
    if ($cnt!=($count?1:0)) { # if this differs from the requested
      $sth=$dbh->prepare("SELECT T.ACTIVE, T.AUTHOR, T.WWHEN FROM ${prefix}TR T WHERE T.TID=?"); # retrieve some global information about the transaction
      $sth->execute($tid);
      my ($active,$author,$wwhen)=$sth->fetchrow_array;
      if ($active || $count==0) { # do not include inactive transactions (but allow temporary exclusion of active ones)
        $sth=$dbh->prepare("UPDATE ${prefix}TR SET COUNTED=? WHERE TID=?"); # update them to reflect the requested inclusion
        $sth->execute($count?1:0,$tid);
        $sth=$dbh->prepare("UPDATE ${prefix}USERS U SET ". # the real magic for the per-user totals
          "TOTALSUM=U.TOTALSUM+((SELECT E.AMOUNT FROM ${prefix}EF E WHERE E.UID=U.UID AND E.TID=?)*?)::NUMERIC(20,10), ".
          "TOTALPCT=U.TOTALPCT+((SELECT E.AMOUNT FROM ${prefix}EF E WHERE E.UID=U.UID AND E.TID=?)*POW($PCT, EXTRACT(EPOCH FROM (U.CREATED - ?)) / $SEC_PER_YEAR)*?)::NUMERIC(20,10) ".
          "WHERE U.UID IN (SELECT E.UID FROM ${prefix}EF E WHERE E.TID=?)"
        );
        $sth->execute($tid,$count?1:(-1),$tid,$wwhen,$count?1:(-1),$tid);
        $sth=$dbh->prepare("SELECT E.UID FROM ${prefix}EF E WHERE E.TID=? AND (SELECT COUNT(*) FROM ${prefix}EDGEINFO I WHERE I.ETO=E.UID AND I.EFROM=? AND I.ETYP='d')=0");
        $sth->execute($tid,$author); # make sure per-edge rows exist for the edges between author and affected ones
        my $sth2;
        while (my ($nuid) = $sth->fetchrow_array) {
          $sth2=$dbh->prepare("INSERT INTO ${prefix}EDGEINFO (ETO,EFROM,ETYP) VALUES (?,?,'d')") if (!defined $sth2); # by creating defaults if necessary
          $sth2->execute($nuid,$author) if ($nuid!=$author);
        }
        $sth=$dbh->prepare("SELECT E.UID FROM ${prefix}EF E WHERE E.TID=? AND (SELECT COUNT(*) FROM ${prefix}EDGEINFO I WHERE I.EFROM=E.UID AND I.ETO=? AND I.ETYP='d')=0");
        $sth->execute($tid,$author); # and the other way around
        while (my ($nuid) = $sth->fetchrow_array) {
          $sth2=$dbh->prepare("INSERT INTO ${prefix}EDGEINFO (ETO,EFROM,ETYP) VALUES (?,?,'d')") if (!defined $sth2); # by creating defaults if necessary
          $sth2->execute($author,$nuid) if ($nuid!=$author);
        }
        $sth=$dbh->prepare("UPDATE ${prefix}EDGEINFO I SET ". # and finally updating those
          "TOTALSUM=I.TOTALSUM+((SELECT E.AMOUNT FROM ${prefix}EF E WHERE E.UID=I.ETO AND E.TID=?)*?)::NUMERIC(20,10), ".
          "TOTALPCT=I.TOTALPCT+((SELECT E.AMOUNT FROM ${prefix}EF E WHERE E.UID=I.ETO AND E.TID=?)*POW($PCT, EXTRACT(EPOCH FROM (I.CREATED - ?)) / $SEC_PER_YEAR)*?)::NUMERIC(20,10) ".
          "WHERE I.EFROM=? AND I.EFROM!=I.ETO AND I.ETO IN (SELECT E.UID FROM ${prefix}EF E WHERE E.TID=?)"
        );
        $sth->execute($tid,$count?1:(-1),$tid,$wwhen,$count?1:(-1),$author,$tid);
        $sth=$dbh->prepare("UPDATE ${prefix}EDGEINFO I SET ". # and the other way around
          "TOTALSUM=I.TOTALSUM+((SELECT E.AMOUNT FROM ${prefix}EF E WHERE E.UID=I.EFROM AND E.TID=?)*?)::NUMERIC(20,10), ".
          "TOTALPCT=I.TOTALPCT+((SELECT E.AMOUNT FROM ${prefix}EF E WHERE E.UID=I.EFROM AND E.TID=?)*POW($PCT, EXTRACT(EPOCH FROM (I.CREATED - ?)) / $SEC_PER_YEAR)*?)::NUMERIC(20,10) ".
          "WHERE I.ETO=? AND I.EFROM!=I.ETO AND I.EFROM IN (SELECT E.UID FROM ${prefix}EF E WHERE E.TID=?)"
        );
        $sth->execute($tid,$count?(-1):1,$tid,$wwhen,$count?(-1):1,$author,$tid);
      }
    }
  } until (defined($locked) || $dbh->commit);
}

# process a request
sub proc_req {
  my ($req,$lock)=@_;
  my $sth=$dbh->prepare("DELETE FROM ${prefix}USERREQ WHERE EXPIRE<CURRENT_TIMESTAMP");
  $sth->execute;
  $dbh->begin_work if (!defined $lock);
  $sth=$dbh->prepare("SELECT UNAME,FULLNAME,ACCNR,EMAIL,HTNAME,PWKEY,LEVEL FROM ${prefix}USERREQ WHERE RID=?");
  $sth->execute($req);
  my $sth2=$dbh->prepare("UPDATE ${prefix}USERS SET ACCNR=? WHERE UID=?");
  my $nuid;
  my $cnt=0;
  while (my ($username,$fullname,$accnr,$email,$htname,$pwkey,$level) = $sth->fetchrow_array) {
    $cnt++;
    $nuid=create_user($username,$fullname,$email,1);
    set_password($pwkey,$nuid,$level,1) if (defined $nuid && defined $pwkey);
    set_htlogin($htname,$nuid,$level,1) if (defined $nuid && defined $htname);
    $sth2->execute($accnr,$nuid) if (defined $nuid && defined $accnr);
  }
  if ($cnt==0) {
    push @msg,['error',"Invalid activation code. It may have been used already, or expired."];
  }
  if (!defined $lock) {
    return $nuid if $dbh->commit;
    return undef;
  }
  return $nuid;
}

# fetch & cache user list
sub need_user_list {
  return if (!defined $auth_username);
  my ($full)=@_;
  if (defined $full) {
    my $sth=$dbh->prepare("SELECT UID,FULLNAME,ACTIVE FROM ${prefix}USERS");
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
    my $sth=$dbh->prepare("SELECT UID,NAME,TOTAL,EXTRA,ACCNR,ACTIVE FROM ${prefix}USERLIST WHERE UID=? OR (UID IN (SELECT SEEN FROM ${prefix}VISIBLE WHERE SEER=? UNION SELECT ETO FROM ${prefix}EDGEINFO WHERE EFROM=? AND (TOTALSUM!=0 OR TOTALPCT!=0) AND ETYP='d')) ORDER BY NAME");
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
    $sth=$dbh->prepare("SELECT SEEN,LEVEL FROM ${prefix}VISIBLE WHERE SEER=? AND SEEN!=SEER");
    $sth->execute($auth_uid);
    while (my ($uid,$level) = $sth->fetchrow_array) {
      if (defined $USERS{$uid}) {
        $USERS{$uid}->{VIS}=$level if ($level>0);
      }
    }
    $sth->finish;
  }
}

# fetch & cache group list
sub need_group_list {
  my ($gidr) = @_;
  my $sth;
  if (defined($gidr)) {
    return if (defined $GROUPS{$gidr});
    $sth=$dbh->prepare("SELECT G.GID,G.DEFINER,G.NAME,G.DESCR,G.ISPUBLIC,G.MAX,G.MAXFORM,G.WWHEN FROM ${prefix}GROUPS G WHERE ((G.DEFINER=?) OR (((SELECT COUNT(*) FROM ${prefix}SHARES S WHERE S.UID=? AND S.GID=G.GID)) > 0)) AND G.GID=? ORDER BY WWHEN");
    $sth->execute($auth_uid,$auth_uid,$gidr);
  } else {
    return if ($haveGROUPS);
    $sth=$dbh->prepare("SELECT G.GID,G.DEFINER,G.NAME,G.DESCR,G.ISPUBLIC,G.MAX,G.MAXFORM,G.WWHEN FROM ${prefix}GROUPS G WHERE ((G.DEFINER=?) OR (((SELECT COUNT(*) FROM ${prefix}SHARES S WHERE S.UID=? AND S.GID=G.GID)) > 0)) AND G.ISPUBLIC ORDER BY WWHEN");
    $sth->execute($auth_uid,$auth_uid);
    $haveGROUPS=1;
  }
  while (my ($gid,$definer,$name,$descr,$ispublic,$max,$maxform,$wwhen) = $sth->fetchrow_array) {
    $GROUPS{$gid}={GID => $gid, DEFINER => $definer, NAME => $name, DESCR => $descr || "",MAX=>$max==0 ? "" : $max,MAXFORM => $maxform,WWHEN=>$wwhen,PUBLIC=>$ispublic,DNAME=>$name."(".substr($wwhen,0,10).")"};
  }
}

sub parsedate {
  my ($str) = @_;
  if ($str =~ /(\d+)-(\d+)-(\d+) (\d+):(\d+):([0-9.]+)/) {
    return timelocal(0,$5,$4,$3,$2-1,$1-1900)+$6;
  } else {
    return time;
  }
}

sub trycommit {
  my ($ok,@npath)=@_;
  my $ret=$dbh->commit;
  if (!$ret) {
    push @msg,['error',"Database error. Try again."];
    return 0;
  } else {
    @path=@npath if ($ok);
    return $ok;
  }
}

sub calculate_active {
  my ($tid,$locked)=@_;
  $dbh->begin_work if (!$locked);
  my $active=1;
  if ($active) { # do not accept things with a deny on them
    my $sth=$dbh->prepare("SELECT COUNT(*) FROM ${prefix}EF E WHERE E.TID=? AND E.ACCEPT=FALSE");
    $sth->execute($tid);
    my ($cnt) = $sth->fetchrow_array;
    $active=0 if ($cnt>0);
  }
  if ($active) { # do not accept things with a price over auto-accept setting of user without an accept
    my $sth=$dbh->prepare("SELECT COUNT(*) FROM ${prefix}EF E, ${prefix}USERS U WHERE E.TID=? AND E.UID=U.UID AND E.ACCEPT IS NULL AND -E.AMOUNT>U.AUTOACCEPT");
    $sth->execute($tid);
    my ($cnt) = $sth->fetchrow_array;
    $active=0 if ($cnt>0);
  }
  if ($active) { # do not accept things whose charge since last accept has been changed by at least the auto-accept value of affected user
    my $sth=$dbh->prepare("SELECT COUNT(*) FROM ${prefix}EF E, ${prefix}USERS U WHERE E.TID=? AND E.UID=U.UID AND E.ACCEPT=TRUE AND E.SEEN-E.AMOUNT>U.AUTOACCEPT");
    $sth->execute($tid);
    my ($cnt) = $sth->fetchrow_array;
    $active=0 if ($cnt>0);
  }
  my $sth=$dbh->prepare("UPDATE ${prefix}TR SET ACTIVE=? WHERE TID=?");
  $sth->execute($active,$tid);
  count_transaction($tid,$active,1);
  trycommit(0) if (!$locked);
  return 1;
}

sub change_accept {
  my ($uid,$am,$x,$tid) = @_;
  return if (!$auth_active);
  my $ok=1;
  $am=0 if (!defined($am));
  $x=1 if (!defined($x));
  $dbh->begin_work;
  my $sth=$dbh->prepare("UPDATE ${prefix}EF SET ACCEPT=?, SEEN=? WHERE UID=? AND TID=?");
  $sth->execute($x,$am,$uid,$tid);
  $ok=calculate_active($tid,1);
  trycommit(0);
  return $ok;
}

sub delete_transaction {
  my ($tid,$typ,$locked) = @_;
  $dbh->begin_work if (!$locked);
  # verify the transaction can be safely removed
  my $sth=$dbh->prepare("SELECT COUNT(*) FROM ${prefix}EF E WHERE E.TID=? AND E.SEEN!=0 AND E.ACCEPT=TRUE");
  $sth->execute($tid);
  my ($cnt)=$sth->fetchrow_array;
  if ($cnt>0) {
    push @msg,['warn',"Cannot delete transaction. Please make sure the transaction has value zero, and that all people involved acknowledge it."];
    $dbh->rollback;
    return 0;
  }
  # do not count transaction
  count_transaction($tid,0,1);
  # effectively remove the transaction and all its effects
  if ($typ eq 'i') {
    $sth=$dbh->prepare("DELETE FROM ${prefix}ITEM WHERE TID=?");
    $sth->execute($tid);
  } elsif ($typ eq 'b') {
    $sth=$dbh->prepare("DELETE FROM ${prefix}BILL WHERE TID=?");
    $sth->execute($tid);
  }
  $sth=$dbh->prepare("DELETE FROM ${prefix}EF WHERE TID=?");
  $sth->execute($tid);
  $sth=$dbh->prepare("DELETE FROM ${prefix}TR WHERE TID=?");
  $sth->execute($tid);
  # delete orphan groups (TODO: speedup by only selecting groups which are affected by deleted statement)
  $sth=$dbh->prepare("SELECT G.GID FROM ${prefix}GROUPS G WHERE G.ISPUBLIC=FALSE AND (SELECT COUNT(*) FROM ${prefix}TR T WHERE T.AFG=G.GID)=0");
  $sth->execute;
  my $sth2=$dbh->prepare("DELETE FROM ${prefix}SHARES WHERE GID=?");
  my $sth3=$dbh->prepare("DELETE FROM ${prefix}GROUPS WHERE GID=?");
  while (my ($dgid) = $sth->fetchrow_array) {
    $sth2->execute($dgid);
    $sth3->execute($dgid);
  }
  return trycommit(1) if (!$locked);
  @path=();
}

sub calculate_effects {
  my ($tid,$locked) = @_;
  my @eff;
  $dbh->begin_work if (!$locked);
  count_transaction($tid,0,1);
  my $sth=$dbh->prepare("SELECT T.TYP,T.AFU,T.AFG,T.AUTHOR FROM ${prefix}TR T WHERE T.TID=?");
  $sth->execute($tid);
  my ($typ,$afu,$afg,$author)=$sth->fetchrow_array;
  if (!defined $typ) {
    push @msg,['error',"Fatal error: transaction $tid does not exist. Contact administrator."];
    $dbh->rollback if (!$locked);
    return 0;
  }
  if ($typ eq 'i') {  # ITEM
    if (defined $afu && defined $afg) {
      push @msg,['error',"Fatal error: item $tid affects both user $afu and group $afg. Contact administrator."];
      $dbh->rollback if (!$locked);
      return 0;
    }
    if (!defined $afu && !defined $afg) {
      push @msg,['error',"Fatal error: item $tid affects neither a user or a group. Contact administrator."];
      $dbh->rollback if (!$locked);;
      return 0;
    }
    $sth=$dbh->prepare("SELECT I.AMOUNT FROM ${prefix}ITEM I WHERE I.TID=?");
    $sth->execute($tid);
    my ($am)=$sth->fetchrow_array;
    if (!defined $am) {
      push @msg,['error',"Fatal error: no item-specific data for transaction $tid. Contact administrator."];
      $dbh->rollback if (!$locked);;
      return 0;
    }
    if (defined $afu) {
      push @eff,[$afu,-1,1,$am];
    } else {
      $sth=$dbh->prepare("SELECT SUM(S.AMOUNT), G.MAX FROM ${prefix}GROUPS G, ${prefix}SHARES S WHERE G.GID=? AND S.GID=? GROUP BY G.MAX");
      $sth->execute($afg,$afg);
      my ($tot,$max) = $sth->fetchrow_array;
      $tot=0 if (!defined $tot);
      $max=0 if (!defined $max);
      $max=$tot if ($tot>$max);
      $sth=$dbh->prepare("SELECT S.UID, S.AMOUNT FROM ${prefix}SHARES S WHERE S.GID=?");
      $sth->execute($afg);
      while (my ($uid,$sh) = $sth->fetchrow_array) {
        push @eff,[$uid,-$sh,$max,$am];
      }
    }
  } elsif ($typ eq 'b') {
    $sth=$dbh->prepare("SELECT B.DEFINITION FROM ${prefix}BILL B WHERE B.TID=?");
    $sth->execute($tid);
    my ($def)=$sth->fetchrow_array;
    if (!defined $def) {
      push @msg,['error',"Fatal error: no bill-specific data for transaction $tid. Contact administrator."];
      $dbh->rollback if (!$locked);
      return 0;
    }
    my ($ndef,$err,$tot,$cont,@effects)=process_bill($def,0);
    if (defined $ndef) {
      push @eff,@effects;
    } else {
      # TODO: warning ofzo, ongeldige bill
    }
  } else {
    push @msg,['error',"Fatal error: transaction $tid has unknown type '$typ'. Contact administrator."];
    $dbh->rollback if (!$locked);
    return 0;
  }
  $sth=$dbh->prepare("UPDATE ${prefix}EF SET AMOUNT=0 WHERE TID=?"); # reset all effects to zero
  $sth->execute($tid);
  my $sth1=$dbh->prepare("SELECT COUNT(*) FROM ${prefix}EF WHERE TID=? AND UID=?"); # check whether they exist
  my $sth2=$dbh->prepare("INSERT INTO ${prefix}EF (TID,UID,AMOUNT) VALUES(?,?,((?::NUMERIC(18,10))*?)/?)"); # if not, add them
  my $sth3=$dbh->prepare("UPDATE ${prefix}EF SET AMOUNT=AMOUNT+(((?::NUMERIC(18,10))*?)/?) WHERE TID=? AND UID=?"); # otherwise, update them
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
    $sth=$dbh->prepare("UPDATE ${prefix}EF SET AMOUNT=COALESCE(-(SELECT SUM(E.AMOUNT) FROM ${prefix}EF E WHERE E.TID=?),0) WHERE TID=? AND UID=?");
    $sth->execute($tid,$tid,$author);
  } else {
    $sth=$dbh->prepare("INSERT INTO ${prefix}EF (TID,UID,AMOUNT) VALUES (?,?,COALESCE(-(SELECT SUM(E.AMOUNT) FROM ${prefix}EF E WHERE E.TID=?),0))");
    $sth->execute($tid,$author,$tid);
  }
  calculate_active($tid,1);
  trycommit(0) if (!$locked);
  return 1;
}

# use -2 for invalid, as -1 is already used for admin user
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
        return -2;
      }
    }
  }
  return $uid;
}

sub get_random_names {
  my ($want) = @_;
  my @rn;
  need_user_list;
  my @users=grep {$_ != $auth_uid} (keys %USERS);
  my $num=scalar @users;
  my $rng=$num; $rng=$want if ($rng<$want);
  for my $i (0..$want-1) {
    while (1) {
      my $rn=int(rand($rng));
      my $x=0;
      for my $j (0..$i-1) {
        if ($rn==$rn[$j]) { $x=1; last; }
      }
      if (!$x) {
        $rn[$i]=$rn;
        last;
      }
    }
  }
  my @ret;
  for my $i (0..$want-1) {
    my $v=$rn[$i];
    if ($v==$num) {
      $ret[$i]="Mickey Mouse";
    } elsif ($v==$num+1) {
      $ret[$i]="Buzz Lightyear";
    } elsif ($v==$num+2) {
      $ret[$i]="Homer Simpson";
    } else {
      $ret[$i]=$USERS{$users[$v]}->{NAME};
    }
  }
  return @ret;
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
          if ($pldef =~ /\A(.*?)(\s+)@(-?[0-9]+(?:\.[0-9]+)?)\Z/) {
            $sldef = $2 . '@' . $3;
            $contrib = $3;
            $pldef = $1;
          }
          if ($pldef =~ /\A\$(-?[0-9]+)/) {
            $uid=$1;
            if ($mode==1) { # just expand uid into name
              need_user_list($uid);
              $pldef=$USERS{$uid}->{NAME};
            } elsif ($mode==2) { # expand uid into name, guaranteeing reversability
              need_user_list;
              my $fname=$USERS{$uid}->{NAME};
              if ($fname =~ /\A(.*?)(\s+)(@\-?[0-9]+(?:\.[0-9]+)?)\Z/) { $fname = $1; }
              if ($fname =~ /\A([^,]*?)\s*,/) { $fname = $1; }
              my $ruid=lookup_user($fname);
              if (defined $ruid && $uid==$ruid && (substr($fname,0,1) ne '$')) {
                $pldef = $fname;
              }
            }
          } else {
            $uid=lookup_user($pldef);
            if ($mode==3) {
              if (defined $uid && $uid!=-2) {
                $pldef = '$'.$uid;
              }
              if ($uid==-2) {
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
  print "<div class='page-header'>\n";
  print "<h1>New payment</h1>\n";
  print "</div>\n";
  print "<form class='form-horizontal form-horizontal-condensed' name='addpay' action='".selfurl."' method='post'>\n";
  print "<input type='hidden' name='cmd' value='addpay'>\n";
  print "<div class='control-group'>\n";
  print "<label class='control-label' for='inputUser'>User</label>\n";
  print "<div class='controls'>\n";
  print "<select name='ap_user' id='inputUser'>\n";
  for (sort {lc($a->{NAME}) cmp lc($b->{NAME})} (values %USERS)) {
    print "  <option value='$_->{UID}'>".htmlwrap($_->{NAME})."</option>\n" if (defined($_->{VIS}) && $_->{ACTIVE} && $_->{UID}!=$auth_uid);
  }
  print "</select>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='control-group'>\n";
  print "<label class='control-label' for='inputAmount'>paid me</label>\n";
  print "<div class='controls'>\n";
  print "<div class='input-prepend'>\n";
  print "<span class='add-on'>$UNIT</span>\n";
  print "<input type='number' id='inputAmount' placeholder='0.00' name='ap_value'>\n";
  print "</div>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='control-group'>\n";
  print "<div class='controls'>\n";
  print "<input type='submit' class='btn' value='Add payment'>\n";
  print "</div>\n";
  print "</div>\n";
  print "</form>\n";
}
sub show_form_add_bill {
  return if (!$auth_active);
  print "<div class='page-header'>\n";
  print "<h1>New bill <small> To learn more about bills, see the <a href='".genurl('help','bill')."'>help</a> pages</small></h1>\n";
  print "</div>\n";
  print "<form class='form-horizontal form-horizontal-condensed' name='addbill' action='".selfurl."' method='post'>\n";
  print "<input type='hidden' name='cmd' value='addbill'>\n";
  print "<div class='control-group'>\n";
  print "<label class='control-label' for='billName'>I paid bill</label>\n";
  print "<div class='controls'>\n";
  print "<input type='text' name='ab_name' id='billName' placeholder='name'>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='control-group'>\n";
  print "<label class='control-label' for='billDescription'>with description</label>\n";
  print "<div class='controls'>\n";
  print "<input type='text' name='ab_descr' id='billDescription' placeholder='description'>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='control-group'>\n";
  print "<div class='controls'>\n";
  print "<input type='submit' class='btn' value='Add bill'>\n";
  print "</div>\n";
  print "</div>\n";
  print "</form>\n";
}
sub show_form_add_item {
  return if (!$auth_active);
  need_user_list;
  need_group_list;

  print "<div class='page-header'>\n";
  print "<h1>New item</h1>\n";
  print "</div>\n";
  print "<form class='form-horizontal form-horizontal-condensed' name='addwant' action='".selfurl."' method='post'>\n";
  print "<input type='hidden' name='cmd' value='addwant'>\n";
  print "<div class='control-group'>\n";
  print "<label class='control-label' for='inputItemPrice'>I paid</label>\n";
  print "<div class='controls'>\n";
  print "<div class='input-prepend'>\n";
  print "<span class='add-on'>$UNIT</span>\n";
  print "<input type='number' name='aw_value' id='inputItemPrice' placeholder='0.00'>\n";
  print "</div>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='control-group'>\n";
  print "<label class='control-label' for='inputItemName'>on item</label>\n";
  print "<div class='controls'>\n";
  print "<input type='text' name='aw_name' id='inputItemName' placeholder='item'>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='control-group'>\n";
  print "<label class='control-label' for='inputItemDescription'>with description</label>\n";
  print "<div class='controls'>\n";
  print "<input type='text' id='inputItemDescription' name='aw_descr' placeholder='description'>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='control-group'>\n";
  print "<label class='control-label' for='inputUser'>for user <input type='radio' name='aw_gtype' value='user' checked></label>\n";
  print "<div class='controls'>\n";
  print "<select name='aw_user' id='inputItemForUser'>\n";
  for (sort {lc($a->{NAME}) cmp lc($b->{NAME})} (values %USERS)) {
    print "<option value='$_->{UID}'>".htmlwrap($_->{NAME})."</option>\n" if (defined($_->{VIS}) && $_->{ACTIVE} && $_->{UID}!=$auth_uid);
  }
  print "</select>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='control-group'>\n";
  print "<label class='control-label' for='inputItemGroup'>for new group <input type='radio' name='aw_gtype' value='new'></label>\n";
  print "<div class='controls'>\n";
  print "<input type='text' id='inputItemGroup' name='aw_ng_name' placeholder='group name'>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='control-group'>\n";
  print "<label class='control-label' for='inputItemForGroup'>for existing group <input type='radio' name='aw_gtype' value='old'></label>\n";
  print "<div class='controls'>\n";
  print "<select id='inputItemForGroup'>\n";
  for (sort {$GROUPS{$b}->{WWHEN} cmp $GROUPS{$a}->{WWHEN}} (keys %GROUPS)) {
    if ($GROUPS{$_}->{PUBLIC}) { print "<option value='$GROUPS{$_}->{GID}'>".htmlwrap($GROUPS{$_}->{DNAME})."</option>\n" };
  }
  print "</select>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='control-group'>\n";
  print "<div class='controls'>\n";
  print "<input type='submit' class='btn' value='Add item'>\n";
  print "</div>\n";
  print "</div>\n";
  print "</form>\n";

}
sub show_totals {
  my $sum=0;
  my $imneg=0;
  need_user_list;

  print "<div class='row-fluid'>\n";
  print "<p>The colors are an indication of your account history: red means mostly negative, green mostly positive</p>\n";
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
            print "<p class='lead'>Within ".sprintf("%.0f", $days)." days your ".($e<0 ? "red" : "green")." color will become white, if no transactions occur</p>\n";
            print "<!-- TOTAL: $_->{TOTAL} ; EXTRA: $_->{EXTRA} -->";
          } if ($days <= -2) {
            print "<!-- <p class='lead'>You are ".sprintf("%.0f", -$days)." days beyond neutral. ".($t+$e>0 ? "Accept some money from others!" : "Give some money to others!")." </p> --->\n";
            print "<!-- TOTAL: $_->{TOTAL} ; EXTRA: $_->{EXTRA} -->";
          }
        }
      }
    }
  }
  print "</div>\n";
  print "<div class='row-fluid'>\n";
  print "<div class='span4'>\n";
  print "<div class='page-header'>\n";
  print "<h1>Hall of shame</h1>\n";
  print "</div>\n";
  print "<table class='table table-striped table-condensed'>\n";
  print "<thead>\n";
  print "<tr>\n";
  print "<th width='80%'>Name</th>\n";
  print "<th class='text-align-right' width='20%'>Total</th>\n";
  print "</tr>\n";
  print "</thead>\n";
  print "<tbody>\n";

  for (sort {$a->{ORD} <=> $b->{ORD}} (grep { defined($_->{ORD}) && $_->{ORD}<0 } (values %USERS))) {
    if ($_->{UID}==$auth_uid || ((defined $_->{VIS}) && $_->{ACTIVE})) {
      my $accnr = (defined $_->{ACCNR}) ? " accnr=$_->{ACCNR}" : "";
      if ($_->{TOTAL}>=0.05 || $_->{TOTAL}<=-0.05 || $_->{UID}==$auth_uid) {
        my ($hi1,$hi2)=("","");
        if (defined($auth_uid) && ($_->{UID} == $auth_uid)) {
          ($hi1,$hi2)=("<b>","</b>");
        }
        print "<tr>\n";
        print "<td>$hi1".htmlwrap($_->{NAME})."$hi2</td>\n";
        print "<td class='text-align-right' style=\"background-color:".get_color($_->{EXTRA},226,226,226).";\">$hi1".( sprintf("$UNIT%.2f",$_->{TOTAL}))."<!-- + ".sprintf("%.4f",$_->{EXTRA})."; ".sprintf("%.0f",days_to_neutral($_->{TOTAL},$_->{EXTRA}))." days$accnr -->$hi2</td>\n";
        print "</tr>\n";
      } else {
        print "<!-- ".htmlwrap($_->{NAME}).": total=".sprintf("$UNIT%.2f",$_->{TOTAL})." int=".sprintf("%.4f",$_->{EXTRA})."$accnr -->\n";
      }
    }
    $sum += $_->{TOTAL};
  }
  my $shame=$sum;

  print "</tbody>\n";
  print "</table>\n";
  print "</div>\n";
  print "<!--/span-->\n";
  print "<div class='span4'>\n";
  print "<div class='page-header'>\n";
  print "<h1>Hall of fame</h1>\n";
  print "</div>\n";
  print "<table class='table table-striped table-condensed'>\n";
  print "<thead>\n";
  print "<tr>\n";
  print "<th width='80%'>Name</th>\n";
  print "<th class='text-align-right' width='20%'>Total</th>\n";
  print "</tr>\n";
  print "</thead>\n";
  print "<tbody>\n";

  for (sort {$b->{ORD} <=> $a->{ORD}} (grep { defined($_->{ORD}) && $_->{ORD}>=0 } (values %USERS))) {
    if ($_->{UID}==$auth_uid || ((defined $_->{VIS}) && $_->{ACTIVE})) {
      my $accnr = (defined $_->{ACCNR}) ? " accnr=$_->{ACCNR}" : "";
      if ($_->{TOTAL}>=0.05 || $_->{TOTAL}<=-0.05 || $_->{UID}==$auth_uid) {
        my ($hi1,$hi2)=("","");
        if (defined($_->{UID}) && $_->{UID} == $auth_uid) {
          ($hi1,$hi2)=("<b>","</b>");
        }
        print "<tr>\n";
        print "<td>$hi1".htmlwrap($_->{NAME})."$hi2</td>\n";
        print "<td class='text-align-right' style=\"background-color:".get_color($_->{EXTRA},226,226,226).";\">$hi1".( sprintf("$UNIT%.2f",$_->{TOTAL}))."<!-- + ".sprintf("%.4f",$_->{EXTRA})."; ".sprintf("%.0f",days_to_neutral($_->{TOTAL},$_->{EXTRA}))." days$accnr -->$hi2</td>\n";
        print "</tr>\n";
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
  print "</tbody>\n";
  print "</table>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='row-fluid'>\n";
  print "<h3>Total imbalance: ".sprintf("$UNIT%.2f",-$shame)."</h3>\n";
  print "</div>\n";
}

sub show_unassigned {
  return if (!defined $auth_username);
#  my $sth=$dbh->prepare("SELECT SUM(U.VALUE) FROM ${prefix}UNASS U, ${prefix}WANT W WHERE W.WID=U.WID AND (W.WANTER=? OR (SELECT COUNT(*) FROM ${prefix}SHARES S WHERE S.GID=W.WANTED AND S.UID=? AND S.AMOUNT!=0)>0)");
#  $sth->execute($auth_uid,$auth_uid);
#  my ($sum)=$sth->fetchrow_array;
#  $sth=$dbh->prepare("SELECT U.NAME,U.VALUE,U.WID,U.GID,U.UNASS,U.MAX FROM ${prefix}UNASS U, ${prefix}WANT W WHERE W.WID=U.WID AND (W.WANTER=? OR (SELECT COUNT(*) FROM ${prefix}SHARES S WHERE S.GID=W.WANTED AND S.UID=? AND S.AMOUNT!=0)>0)");
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
  my $sth=$dbh->prepare("SELECT U.UNAME, U.FULLNAME, U.ACCNR, U.EMAIL, U.TOTALSUM, U.CREATED, U.AUTOACCEPT FROM ${prefix}USERS U WHERE UID=?");
  $sth->execute($auth_uid);
  my ($uname,$fullname,$accnr,$email,$total,$created,$autoaccept)=$sth->fetchrow_array;
  print "<h3>Profile settings:</h3>\n";
  print "<form name='chprofile' action='".selfurl."' method='post'>\n";
  print "<table>";
  print "<tr class='tblodd'><td>User name:</td><td></td><td>".htmlwrap($uname)."</td></tr>\n";
  print "<tr class='tbleven'><td>Full name:</td><td></td><td><input type='text' name='cp_fullname' value='".htmlwrap($fullname)."' /></td></tr>\n";
  print "<tr class='tblodd'><td>Bank account number:</td><td></td><td><input type='text' name='cp_accnr' value='".htmlwrap($accnr)."' /></td></tr>\n";
  print "<tr class='tbleven'><td>By default, deny charges above:</td><td></td><td><input type='text' size='7' name='cp_autoaccept' value='".htmlwrap($autoaccept)."' /> EUR</td></tr>\n";
  print "<tr class='tblodd'><td>E-mail address:</td><td></td><td>".htmlwrap($email)."</td></tr>\n";
  print "<tr class='tbleven'><td>Account balance:</td><td></td><td style='color:".($total>=0 ? 'black' : 'red')."'>".sprintf("$UNIT %.4f",abs($total))."</td></tr>\n";
  print "<tr class='tblodd'><td>Creation date:</td><td></td><td>".htmlwrap(substr($created,0,16))."</td></tr>\n";
  print "</table>\n";
  print "<input type='hidden' name='cmd' value='chprof' />\n";
  print "<input type='submit' value='Change settings' />\n";
  print "</form>\n";
  print "<p/>\n";
}

sub show_change_password {
  print "<h3>Change password:</h3>\n";
  print "<form name='chpasswd' action='".selfurl."' method='post'>\n";
  print "<table>";
  print "<tr class='tblodd'><td>Old password </td><td><input type='password' name='password' size=10 /></td></tr>\n";
  print "<tr class='tbleven'><td>New password: </td><td><input type='password' name='newpass1' size=10 /></td></tr>\n";
  print "<tr class='tblodd'><td> Repeat: </td><td><input type='password' name='newpass2' size=10 /></td></tr>\n";
  print "</table>\n";
  print "<input type='hidden' name='cmd' value='chpass' />\n";
  print "<input type='hidden' name='username' value='".(htmlwrap($auth_username))."' />\n";
  print "<input type='submit' value='Change password' />\n";
  print "</form>\n";
  print "<br>\n";
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

sub show_history_line {
  my ($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid,$active,$num,$showch) = @_;
  my $st=($active ? "" : "text-decoration: line-through; ");
  print "<tr>\n";
  print "<td style='$st'>".(substr($wwhen,0,16) || "never")."</td>\n";
  print "<td style='$st'>";
  my $descr=describe($amount,$name,$author,$affectuid,$affectgid,$type,$tid);
  print $descr;
  print "</td>\n";
  print "<td class='text-align-right'>";
  print "<a style='color:".($amount>=0 ? 'black' : 'red')."; $st' title=\"".htmlwrap($amount)."\">".sprintf("$UNIT%.2f",abs($amount))."</a>\n";
  print "</td>";
  my $raccept=$accept;
  if (!defined($raccept) || $amount<$seen) {
    $raccept=$amount+$auth_autoaccept>$seen;
  }
  my $changed=abs($amount-$seen)>=$THRESHOLD;
  print "<td class='text-align-center' style='$st'>";
  print "<input type='checkbox' name='hlx_$tid' value='1' ".($raccept ? '' : 'checked')." />";
  print "<input type='hidden' name='hlv_$tid' value='".($showch ? $amount : $seen)."' />";
  print "<input type='hidden' name='hlo_$tid' value='".((!defined $accept || ($showch && $changed)) ? "-1" : ($raccept ? "0" : "1"))."' />";
  print "</td>";
  if ($showch) {
    my $color=$amount>$seen ? 'black' : 'red';
    print "<td style='color:$color; $st'>";
    if ($changed) {
      if ($seen==0 && !defined($accept)) {
        print "NEW";
      } else {
        print sprintf("$UNIT %.2f",abs($amount-$seen)) 
      }
    }
    print "</td>"
  }
  print "</tr>\n";
  return "$tid";
}

sub show_warn {
  need_user_list;
  my $sth=$dbh->prepare("SELECT E.AMOUNT,E.SEEN,E.ACCEPT,T.NAME,T.AUTHOR,T.AFU,T.AFG,T.WWHEN,T.TYP,T.TID,T.ACTIVE FROM ${prefix}EF E, ${prefix}TR T WHERE E.UID=? AND T.TID=E.TID AND (ABS(E.AMOUNT-E.SEEN)>=? OR E.ACCEPT=FALSE OR (T.ACTIVE=FALSE AND T.AUTHOR=E.UID)) ORDER BY WWHEN DESC");
  $sth->execute($auth_uid,$THRESHOLD);
  my $warned=0;
  my $changes=0;
  my $num=0;
  my @ids=();
  print "<div class='row-fluid'>\n";
  print "<div class='span8'>\n";
  print "<div class='page-header'>\n";
  print "<h1>Notifications for ".htmlwrap($auth_fullname)."</h1>\n";
  print "</div>\n";
  while (my ($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid,$active) = $sth->fetchrow_array) {
    if (!$warned) {
      print "<form name='editwarn' action='".selfurl."' method='post'>\n";
      print "<table class='table table-condensed table-striped'>\n";
      print "<thead>\n";
      print "<tr>\n";
      print "<th>Date</th>\n";
      print "<th>Reason</th>\n";
      print "<th class='text-align-right'>Amount</th>\n";
      print "<th class='text-align-center'>Denied</th>\n";
      print "<th>Changed</th>\n";
      print "</tr>\n";
      print "</thead>\n";
      print "<tbody>\n";
      $warned=1;
    }
    push @ids,show_history_line($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid,$active,$num++,1);
    if (abs($seen-$amount)>$THRESHOLD) {
      $changes++;
    }
  }
  if ($warned) {
    print "</tbody>\n";
    print "</table>\n";
    print "<input type='hidden' name='hl_ids' value='".join(',',@ids)."' />\n";
    print "<input type='hidden' name='cmd' value='dohl' />\n";
    print "<input type='submit' class='btn' value='Acknowledge'/>\n";
    print "</form>\n";
  } else {
    print "No notifications at this time.\n";
  }
  print "</div>\n";
  print "</div>\n";
  return 1;
}

sub show_history {
  my ($all)=@_;
  my $sth;
  need_user_list;
  print "<div class='row-fluid'>\n";
  print "<div class='span8'>\n";
  print "<div class='page-header'>\n";
  if (defined $all) {
    print "<h1>Full history</h1>\n";
  } else {
    print "<h1>Recent history</h1>\n";
  }
  print "</div>\n";

  print "<form name='edithistory' action='".selfurl."' method='post'>\n";

  print "<table class='table table-striped table-condensed'>\n";
  print "<thead>\n";
  print "<tr>\n";
  print "<th>Date</th>\n";
  print "<th>Reason</th>\n";
  print "<th class='text-align-right'>Amount</th>\n";
  print "<th class='text-align-center'>Denied</th>\n";
  print "</tr>\n";
  print "</thead>\n";
  print "<tbody>\n";
  $sth=$dbh->prepare("SELECT E.AMOUNT,E.SEEN,E.ACCEPT,T.NAME,T.AUTHOR,T.AFU,T.AFG,T.WWHEN,T.TYP,T.TID,T.ACTIVE FROM ${prefix}EF E, ${prefix}TR T WHERE E.UID=? AND T.TID=E.TID ORDER BY T.WWHEN DESC".($all ? "" : " LIMIT 50"));
  $sth->execute($auth_uid);
  my @ids=();
  my $num=0;
  while (my ($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid,$active) = $sth->fetchrow_array) {
    push @ids,show_history_line($amount,$seen,$accept,$name,$author,$affectuid,$affectgid,$wwhen,$type,$tid,$active,$num++,0);
  }
  $sth->finish;
  print "</tbody>\n";
  print "</table>\n";
  print "<input type='hidden' name='hl_ids' value='".join(',',@ids)."' />\n";
  print "<input type='hidden' name='cmd' value='dohl' />\n";
  print "<input type='submit' class='btn' value='Change denies' />\n";
  print "</form>\n";
  print "</div>\n";
  print "</div>\n";

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

# output html header
sub output_header {
  my @cookies=();
  if (defined $session) {
    my %cookiedata=(-name => 'session', -value => $session, -domain => $ENV{SERVER_NAME}, -path => $DIR, -expires => "+${SESSION_TIME}m");
    #log_action "COOKIE: ".(join('|',%cookiedata));
    push @cookies,cookie(%cookiedata);
  }
  print header(-cookie => \@cookies,-charset=>'UTF-8',-type => 'text/html');
  print "<!DOCTYPE html>\n";
  print "<html>\n";
  print "<head>\n";
  print "<meta charset=\"utf-8\">\n";
  print "<link href='css/bootstrap.css' rel='stylesheet'>\n";
  print "<link href='css/bootstrap-responsive.css' rel='stylesheet'>\n";
  print "<link href='css/custom.css' rel='stylesheet'>\n";
  print "<link rel='alternate' type='application/rss+xml' title='RSS' href='".genurl('rss')."' />\n";
  print "<title>$title".(defined $auth_username ? (" - ".htmlwrap($auth_username)) : "")."</title>\n";
  print "</head>\n";
  print "<body>\n";
  print "<div class='navbar navbar-inverse navbar-fixed-top'>\n";
  print "<div class='navbar-inner'>\n";
  print "<div class='container-fluid'>\n";
  print "<a class='brand' href=\"$URL\">$htmltitle</a>\n";
  print "<ul class='nav pull-right'>\n";
  print "<li><p class='navbar-text'>Logged in as ".htmlwrap($auth_fullname)." (".htmlwrap($auth_username).") </p></li>\n" if (defined $auth_username);
  print "</ul>\n";
  print "</div>\n";
  print "</div>\n";
  print "</div>\n";
  print "<div class='container-fluid'>\n";
  print "<div class='row-fluid'>\n";
  print "<div class='span2'>\n";
  print "<div class='well sidebar-nav'>\n";
  print "<ul class='nav nav-list'>\n";
  print "<li class='nav-header'>Menu</li>\n";
  print "<li ".($path[0] eq 'overview' ? 'class="active"' : '')."><a accesskey=\"o\" href=\"$URL\">Overview</a></li>\n" if (defined $auth_username);
  print "<li ".($path[0] eq 'add' ? 'class="active"' : '')."><a accesskey=\"a\" href=\"".genurl('add')."\">New transaction</a></li>\n" if (defined $auth_username);
  print "<li ".($path[0] eq 'connections' ? 'class="active"' : '')."><a accesskey=\"c\" href=\"".genurl('connections')."\">Connections</a></li>\n"if (defined $auth_username);
  print "<li ".($path[0] eq 'history' ? 'class="active"' : '')."><a accesskey=\"h\" href=\"".genurl('history')."\">Full history</a></li>\n"if (defined $auth_username);
  print "<li ".($path[0] eq 'payment' ? 'class="active"' : '')."><a href=\"".selfurl."\">Payment</a></li>\n" if (defined $auth_username && $path[0] eq 'payment');
  print "<li ".($path[0] eq 'item' ? 'class="active"' : '')."><a href=\"".selfurl."\">Item</a></li>\n" if (defined $auth_username && $path[0] eq 'item');
  print "<li ".($path[0] eq 'group' ? 'class="active"' : '')."><a href=\"".selfurl."\">Group</a></li>\n" if (defined $auth_username && $path[0] eq 'group');
  print "<li ".($path[0] eq 'bill' ? 'class="active"' : '')."><a href=\"".selfurl."\">Bill</a></li>\n" if (defined $auth_username && $path[0] eq 'bill');
  print "<li ".($path[0] eq 'settings' ? 'class="active"' : '')."><a accesskey=\"s\" href=\"".genurl('settings')."\">Settings</a></li>\n" if (defined $auth_username);
  print "<li>&nbsp;</li>\n";
  print "<li ".($path[0] eq 'activate' ? 'class="active"' : '')."><a href=\"".selfurl."\">Account activation</a></li>\n" if (defined $path[0] && $path[0] eq 'activate');
  print "<li ".($path[0] eq 'help' ? 'class="active"' : '')."><a accesskey=\"?\" href=\"".genurl((defined $path[0] && $path[0] eq 'help') ? 'help' : ('help',@path))."\">Help</a></li>\n";
  print "<li>&nbsp;</li>\n";
  print "<li ".($path[0] eq 'logout' ? 'class="active"' : '')."><a accesskey=\"x\" href=\"".genurl('logout')."\">Log out</a></li>\n" if (defined $auth_username || defined $session);
  print "<li ".($path[0] eq 'login' ? 'class="active"' : '')."><a href=\"".genurl('login')."\">Log in</a></li>\n" if ((defined $path[0] && $path[0] eq 'login') || !defined $auth_username);
  print "</ul>\n";
  print "</div>\n";
  print "<!--/.well -->\n";
  print "</div>\n";
  print "<!--/span-->\n";
  print "<div class='span10'>\n";
  print "<div class='container-fluid'>\n";
  for my $msg (@msg) {
    print "<div class='alert alert-$msg->[0]'>$msg->[1]</div>\n";
  }
}

sub output_footer {
  print "</div>\n";
  print "</div>\n";
  print "<!--/span-->\n";
  print "</div>\n";
  print "<!--/row-->\n";
  print "<hr>\n";
  print "<footer>\n";
  print "<p class='pull-right'>&copy; 2006-2012 by Pieter Wuille & Samuel Van Reeth powered by $VERSION</p>\n";
  print " </footer>\n";
  print "</div>\n";
  print "<!--/.fluid-container-->\n";
  print "<script src='js/jquery.js'></script>\n";
  print "<script src='js/bootstrap.js'></script>\n";
  print "</body>\n";
  print "</html>\n";
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
connect_db;

# handle commands
my $command=param('cmd') || $ARGV[0] || "";
if ($command eq 'reset') {
  init_db;
  exit;
}

# check for initdb
if ($CONF{initdb}) {
  my $cmd=$0 || $ENV{SCRIPT_NAME};
  push @msg,['error',"Please initialize the database first, using<br/>\n".
        "  <tt>./$cmd reset</tt>\n".
        "and disable the initdb option in kas.conf before continuing.\n"];
  output_header;
  output_footer;
  exit;
}

# handle authentication
check_auth;

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
  if (defined ($meth) && $meth eq 'pw') {
    if (length($user) < 4) { $ok=0; push @msg,['warn',"Username too short (need at least 4 character)"]; }
    if (length($pass1) < 6) { $ok=0; push @msg,['warn',"Password too short (need at least 6 characters)"]; }
    if ($pass1 ne $pass2) { $ok=0; push @msg,['warn',"Passwords don't match"]; }
  } elsif (defined ($meth) && $meth eq 'ht') {
    if (!defined $ENV{REMOTE_USER}) { $ok=0; push @msg,['warn',"No user logged in"] }
  } else  {
    { $ok=0; push @msg,['error',"Unknown authentication method '".htmlwrap($meth)."' requested"]; }
  }
  if ($ok) {
    my $rid=generate_sid(160);
    my $sth=$dbh->prepare("INSERT INTO ${prefix}USERREQ (RID,UNAME,FULLNAME,ACCNR,EMAIL,HTNAME,PWKEY,LEVEL) VALUES (?,?,?,?,?,?,?,?)");
    my $res=0;
    if ($meth eq 'pw') {
      $res=$sth->execute($rid,$user,$fullname,$accnr,$email,undef,gen_key($pass1),1);
    } elsif ($meth eq 'ht') {
      $res=$sth->execute($rid,$ENV{REMOTE_USER},$fullname,$accnr,$email,$ENV{REMOTE_USER},undef,1);
    }
    if ($res==0) {
      $ok=0;
      push @msg,['error',"Cannot add user, try again or inform administrator"];
    }
    if ($ok) {
      # $ok=open(PIPE,"|mail -s 'New account: $title' ".(defined($mailfrom) ? "-a 'From: $mailfrom'" : "")." '$email'");
      # if ($ok) { print PIPE "Hello $fullname,\n\na new $title account has been created for you.\nTo activate it, use this link:\n\n  ".url(-base=>1).genurl('activate',$rid)."\n\n-- \nKind regards,\n$title mailer\n"; }
      # $ok=(close PIPE) if ($ok);
      push @msg,['info',"An activation code was mailed to ".htmlwrap($email).". It will remain valid for a week."] if ($ok);
      push @msg,['error',"Could not send e-mail. Try again or contact administrator."] if (!$ok);
    }
  }
  @path=('empty') if ($ok);
}
if ($command eq 'chprof' && defined $auth_username) {
  my $accnr=param('cp_accnr') || undef;
  my $fname=param('cp_fullname');
  my $axept=param('cp_autoaccept') || 50;
  my $ok=1;
  if (!defined $fname || $fname =~ /\A\s*\Z/) {
    push @msg,['warn',"Full name cannot be empty"];
    $ok=1;
  }
  if ($ok) {
    my $sth=$dbh->prepare("UPDATE ${prefix}USERS SET FULLNAME=?, ACCNR=?, AUTOACCEPT=? WHERE UID=?");
    $ok=$sth->execute(normalize_name($fname),$accnr,$axept,$auth_uid);
  }
  if ($ok) {
    push @msg,['info',"Profile changed"];
    @path=();
  } else {
    push @msg,['error',"Could not change profile"];
  }
}
if ($command eq 'chpass' && defined $auth_username) {
  my $sth=$dbh->prepare("SELECT UNAME FROM ${prefix}USERS WHERE UID=? LIMIT 1");
  $sth->execute($auth_uid);
  my ($username) = $sth->fetchrow_array();
  my $ok=1;
  check_auth($username); # re-check auth based on username/password
  if ($auth_level < $MIN_LEVEL_NOPASSSUDO && index($auth_methods,'|password|')<0) {
    push @msg,['error',"Invalid old password"];
    $ok=0;
  }
  if (param('newpass1') ne param('newpass2')) {
    push @msg,['error',"Passwords do not match"];
    $ok=0;
  }
  if (length(param('newpass1'))<6) {
    push @msg,['error',"New password is too short"];
    $ok=0;
  }
  if ($ok) {
    if (set_password(gen_key(param('newpass1')))) {
      push @msg,['info',"Your password was succesfully changed"];
      @path=();
    } else {
      push @msg,['error',"Your password was not changed"];
    }
  }
}
if ($command eq 'dohl' && defined $auth_username) {
  my @ids=split(/,/,param('hl_ids'));
  foreach my $id (@ids) {
    my $x=param("hlx_$id") ? 1 : 0;
    my $am=param("hlv_$id");
    my $o=param("hlo_$id");
    if (defined $x && defined $am && defined $o && $x!=$o) {
      change_accept($auth_uid,$am,1-$x,$id);
    }
  }
}
if ($command eq 'addpay' && defined $auth_username) { while(1) {
  my $c_value = calc(param('ap_value'));
  if (!defined $c_value || $c_value<=0) {
    push @msg,["error","Invalid amount for payment: ".htmlwrap(param('ap_value') || "")];
    last;
  }
  my ($u1,$u2,$val)=(param('ap_user'),$auth_uid,$c_value);
  need_user_list;
  if (!defined $USERS{$u1}->{VIS}) {
    push @msg,['warn',"Please select a user"];
    last;
  }
  my $sth=$dbh->prepare("SELECT nextval('${prefix}NTR')");
  $sth->execute;
  my ($tid) = $sth->fetchrow_array;
  $dbh->begin_work;
  $sth=$dbh->prepare("INSERT INTO ${prefix}TR (tid,author,afu,typ) values (?,?,?,'i')");
  $sth->execute($tid,$u2,$u1);
  $sth=$dbh->prepare("INSERT INTO ${prefix}ITEM (tid,amount) values (?,?)");
  $sth->execute($tid,-$val);
  calculate_effects($tid,1);
  if (trycommit(1)) {
    push @msg,['info',"Payment succesfully added"];
  }
  log_action("add pay from=$u1 to=$u2 amount='".param('ap_value')."'");
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
  my $sth=$dbh->prepare("SELECT nextval('${prefix}NTR')");
  $sth->execute;
  my ($tid)=$sth->fetchrow_array;
  if (param('aw_gtype') eq 'new') {
    my $sth=$dbh->prepare("SELECT nextval('${prefix}NGROUPS')"); # nextval outside SQL transaction
    $sth->execute;
    $gid=$sth->fetchrow_array;
    $dbh->begin_work;
    $sth=$dbh->prepare("INSERT INTO ${prefix}GROUPS (GID,DEFINER,NAME) VALUES (?,?,?)");
    $sth->execute($gid,$auth_uid,param('aw_ng_name') || 'group');
    log_action("create group gid=$gid name='".param('aw_ng_name')."'");
  } elsif (param('aw_gtype') eq 'user') {
    $uid=param('aw_user');
    need_user_list;
    if (!$USERS{$uid}->{VIS}) {
      push @msg,['warn',"Invalid user for adding item"];
      last;
    }
    $dbh->begin_work;
  } else {
    $gid=param('aw_group');
    need_group_list($gid || 0);
    if (!defined $GROUPS{$gid}) {
      push @msg,['warn',"Invalid group for adding item"];
    }
    $dbh->begin_work;
  } 
  $sth=$dbh->prepare("INSERT INTO ${prefix}TR (TID,AUTHOR,AFG,AFU,NAME,DESCR,TYP) VALUES (?,?,?,?,?,?,'i')");
  $sth->execute($tid,$auth_uid,$gid,$uid,param('aw_name'),param('aw_descr'));
  $sth=$dbh->prepare("INSERT INTO ${prefix}ITEM (TID,AMOUNT) VALUES (?,?)");
  $sth->execute($tid,$c_value);
  calculate_effects($tid,1);
  log_action("add want wanter=$auth_uid ".(defined $gid ? "gid=$gid" : "")." ".(defined $uid ? "uid=$uid" : "") . " amount='".param('aw_value')."'(".calc(param('aw_value')).") name='".param('aw_name')."' descr='".param('aw_descr')."'");
  if (param('aw_gtype') eq 'new') {
    trycommit(1,'group',$gid);
  } else {
    trycommit(1);
  }
  last;
} }
if ($command eq 'addbill' && defined $auth_username) { while(1) {
  my $sth=$dbh->prepare("SELECT nextval('${prefix}NTR')");
  $sth->execute;
  my ($tid)=$sth->fetchrow_array;
  $dbh->begin_work;
  $sth=$dbh->prepare("INSERT INTO ${prefix}TR (TID,AUTHOR,NAME,DESCR,TYP) VALUES (?,?,?,?,'b')");
  $sth->execute($tid,$auth_uid,param('ab_name'),param('ab_descr'));
  $sth=$dbh->prepare("INSERT INTO ${prefix}BILL (TID,DEFINITION) VALUES (?,'')");
  $sth->execute($tid);
  log_action("create bill tid=$tid name='".param('ab_name')."' descr='".param('ab_descr')."'");
  calculate_effects($tid,1);
  trycommit(1,'bill',$tid);
  last;
} }
if ($command eq 'doeg' && defined $auth_username) { while(1) {
  exit if (!$auth_active);
  my $dgid=param('eg_gid');
  need_group_list($dgid || 0);
  if (!defined $GROUPS{$dgid}) {
    push @msg,['warn',"Access denied while editing group"];
    last;
  }
  need_user_list;
  $dbh->begin_work;
  my $ok=1;
  my %uids;
  my $sth=$dbh->prepare("SELECT UID,FORMULA FROM ${prefix}SHARES WHERE GID=?");
  $sth->execute($dgid);
  while (my ($uid,$form) = $sth->fetchrow_array) {
    $uids{$uid}=[$form,calc($form)];
  }
  $sth=$dbh->prepare("DELETE FROM ${prefix}SHARES WHERE GID=?");
  $sth->execute($dgid);
  my @ass;
  my $maxval=calc(param('eg_max') || 0);
  if (!defined $maxval) {
    push @msg,['warn',htmlwrap(param('eg_max')) . " is not a valid expression for &quot;max assignments&quot;"];
    $ok=0;
  }
  my $gcd=int($maxval*$DENOM+0.5);
  if (defined(param('eg_uids'))) {
    foreach my $uid (split(/,/,param('eg_uids'))) {
      if (defined($USERS{$uid}) && defined(param("eg_a$uid"))) {
        my $clc=calc(param("eg_a$uid"));
        if (!defined $clc) {
          push @msg,['warn',htmlwrap(param("eg_a$_")). " is not a valid expression"];
          $ok=0;
        } else {
          $uids{$uid}=[param("eg_a$uid"),$clc];
        }
      }
    }
    foreach my $uid (keys %uids) {
      my $val=int($uids{$uid}->[1]*$DENOM+0.5);
      $gcd = ($gcd==0 ? $val : gcd($val,$gcd)) if ($val>0);
    }
    $gcd=1 if ($gcd<=0);
    if ($ok) { 
      $sth=$dbh->prepare("INSERT INTO ${prefix}SHARES (GID,UID,FORMULA,AMOUNT) VALUES (?,?,?,?)");
      for my $uid (keys %uids) {
        my $val=int(($DENOM*$uids{$uid}->[1]+0.5)/$gcd);
        $sth->execute($dgid,$uid,$uids{$uid}->[0],$val) if ($val>0);
        push @ass,"$uid=>'".param("eg_a$uid")."'($val; den=$DENOM, gcd=$gcd, calc=".$uids{$uid}->[1].")";
      }
    }
  }
  if ($ok) {
    my $mmax=int($maxval*$DENOM+0.5)/$gcd; $mmax=0 if ($mmax<0);
    $sth=$dbh->prepare("UPDATE ${prefix}GROUPS SET NAME=?,DESCR=?,MAX=?,MAXFORM=?,ISPUBLIC=? WHERE GID=?");
    $sth->execute(param('eg_name')||'-',param('eg_descr')||'',$mmax,param('eg_max'),param('eg_public')||0,$dgid);
    my $sthx=$dbh->prepare("SELECT TID FROM ${prefix}TR WHERE AFG=?");
    $sthx->execute($dgid);
    while (my ($tid) = $sthx->fetchrow_array) {
      calculate_effects($tid,1);
    }
    if (trycommit($ok)) {
      log_action("update group gid=$dgid name='".(param('eg_name')||'-')."' descr='".(param('eg_descr')||'')."' max=$mmax invis=".(param('eg_invis')||0)." ass=(".join(',',@ass).")");
      push @msg,['info',"Group succesfully modified"];
    }
  } else {
    $dbh->rollback;
  }
  last;
} }
if ($command eq 'doep' && defined $auth_username) { while(1) {
  my $clc=calc(param('ep_value'));
  if (!defined $clc) {
    push @msg,['warn',htmlwrap(param('ep_value') || "") . " is not a valid amount for payment"];
    last;
  }
  my $tid=param('ep_id');
  my $sth=$dbh->prepare("SELECT T.AUTHOR,T.AFU,T.WWHEN,I.AMOUNT FROM ${prefix}TR T, ${prefix}ITEM I WHERE T.TID=? AND I.TID=? AND T.NAME IS NULL");
  $sth->execute($tid,$tid);
  my ($pfrom,$pto,$wwhen,$amount)=$sth->fetchrow_array;
  my $ok=1;
  my $dodel=0;
  if (defined $pfrom && $pfrom==$auth_uid) {
    if (param('ep_delete')) {
      delete_transaction($tid,'i',0);
      last;
    }
    $dbh->begin_work;
    $sth=$dbh->prepare("UPDATE ${prefix}ITEM SET AMOUNT=? WHERE TID=?");
    $ok=$sth->execute(-$clc,$tid);
    push @msg,['warn',"Could not modify payment"] if (!$ok);
    calculate_effects($tid,1);
    if (trycommit($ok)) {
      push @msg,['info',"Payment succesfully ".($dodel ? "deleted" : "modified")];
    }
  } else {
    if (!defined $pfrom) {
      push @msg,['error',"Payment does not exist"];
      @path=();
    } else {
      push @msg,['error',"Permission denied while editing payment"];
    }
  }
  last;
} }
if ($command eq 'doeb' && defined $auth_username) { while(1) {
  my $tid=param('eb_id');
  my $sth=$dbh->prepare("SELECT T.AUTHOR,T.WWHEN,B.DEFINITION FROM ${prefix}TR T, ${prefix}BILL B WHERE T.TID=? AND B.TID=?");
  $sth->execute($tid,$tid);
  my ($pfrom,$wwhen,$def)=$sth->fetchrow_array;
  my $ok=1;
  my $dodel=0;
  if (defined $pfrom && $pfrom==$auth_uid) {
    if (param('eb_delete')) {
      delete_transaction($tid,'b',0);
      last;
    }
    my $def=param('eb_def');
    need_user_list;
    my ($ndef,$err)=process_bill($def,3);
    last if (!defined $ndef);
    $dbh->begin_work;
    $sth=$dbh->prepare("UPDATE ${prefix}BILL SET DEFINITION=? WHERE TID=?");
    $ok=$sth->execute($ndef,$tid);
    if ($ok) {
      $sth=$dbh->prepare("UPDATE ${prefix}TR SET NAME=?, DESCR=? WHERE TID=?");
      $ok &&= $sth->execute(param('eb_name'),param('eb_descr'),$tid);
    }
    push @msg,['error',"Could not modify bill"] if (!$ok);
    calculate_effects($tid,1);
    if (trycommit($ok && !$err)) {
      push @msg,['info',"Bill succesfully ".($dodel ? "deleted" : "modified")];
    }
  } else {
    if (!defined $pfrom) {
      push @msg,['error',"Bill does not exist"];
      @path=();
    } else {
      push @msg,['error',"Permission denied while editing bill"];
    }
  }
  last;
} }
if ($command eq 'doew' && defined $auth_username) { while(1) {
  my $clc=calc(param('ew_value'));
  if (!defined $clc) {
    push @msg,['warn',htmlwrap(param('ew_value') || "") . " is not valid amount for item"];
    last;
  }
  my $tid=param('ew_id');
  my $sth=$dbh->prepare("SELECT T.AUTHOR,T.AFG,T.WWHEN,I.AMOUNT FROM ${prefix}TR T, ${prefix}ITEM I WHERE T.TID=? AND I.TID=?");
  $sth->execute($tid,$tid);
  my ($wanter,$wanted,$wwhen,$amount)=$sth->fetchrow_array;
  $sth->finish;
  my $ok=1;
  if (defined($wanter) && $wanter==$auth_uid) {
    if (param('ew_delete')) {
      delete_transaction($tid,'i',0);
      last;
    }
    $dbh->begin_work;
    $sth=$dbh->prepare("UPDATE ${prefix}TR SET NAME=?,DESCR=? WHERE TID=?");
    $sth->execute(param('ew_name'),param('ew_descr'),$tid);
    $sth=$dbh->prepare("UPDATE ${prefix}ITEM SET AMOUNT=? WHERE TID=?");
    $sth->execute($clc,$tid);
    log_action("edit want tid=$tid wanter=$wanter wanted=$wanted amount='".(param('ew_value')||0)."' wwhen='$wwhen' name='".(param('ew_name')||"")."' descr='".(param('ew_descr')||"")."'");
    calculate_effects($tid,1);
    trycommit($ok);
  }
  last;
} }
if ($command eq 'doev' && defined $auth_username) {
  need_user_list;
  for my $uid (split(/,/,param('ev_uids'))) {
    my $par=param("ev_u$uid");
    my $vis=(defined($par) && $par==1) ? 1 : 0;
    if ($uid!=$auth_uid && (($vis>0) != (defined($USERS{$uid}->{VIS})))) {
      my $sth=$dbh->prepare("DELETE FROM ${prefix}VISIBLE WHERE (SEER=? AND SEEN=?) OR (SEER=? AND SEEN=?)");
      $sth->execute($auth_uid,$uid,$uid,$auth_uid);
      $sth=$dbh->prepare("INSERT INTO ${prefix}VISIBLE (SEER,SEEN,LEVEL) VALUES (?,?,?)");
      $sth->execute($auth_uid,$uid,$vis);
      $sth->execute($uid,$auth_uid,$vis);
      if ($vis>0) {
        $USERS{$uid}->{VIS}=$vis;
      } else {
        delete $USERS{$uid}->{VIS};
      }
      $sth->finish;
      log_action("visibility $uid to $vis");
    }
  }
  $haveUSERS=0;
}
if (defined $path[0] && (($path[0] eq 'logout') || $path[0] eq 'activate')) {
  if (defined $session) {
    my $sth=$dbh->prepare("DELETE FROM ${prefix}SESSION WHERE SID=?");
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

if (defined $auth_username && !$auth_active) {
  push @msg,['warn',"Your account is currently locked. No manipulation of transactions is possible. Contact administrator to have your account unlocked."];
}

# handle web interface 
while(1) {
  my $menu=$path[0];
  $menu='default' if (!defined $menu || $menu eq '');
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
    print "rel url: ".url(-relative=>1)."\n";
    print "ful url: ".url(-full=>1)."\n";
    print "bas url: ".url(-base=>1)."\n";
  } elsif ($menu eq 'env') {
    print "Content-type: text/plain\n\n";
    while (my ($key,$val)=each %ENV) {
      print "ENV{$key}='$val'\n";
    }
  } elsif ($menu eq 'group' && defined $auth_username) {
    my $grouptoedit=$path[1];
    need_group_list($grouptoedit);
    need_user_list;
    my $gte=$GROUPS{$grouptoedit};
    if (!defined $gte) {
      push @msg,['error',"Group does not exist or permission denied"];
      @path=();
      next;
    }
    my $sth=$dbh->prepare("SELECT UID,AMOUNT,FORMULA from ${prefix}SHARES WHERE GID=?");
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
    print "<form name='doeg' action='".selfurl."' method='post'>\n";
    print "<table>\n";
    print "<tr class='tblodd'><td>Name:</td><td> <input type='text' name='eg_name' value=".'"'.htmlwrap(param('eg_name') || $gte->{NAME}).'"'."></tr></td>\n";
    print "<tr class='tbleven'><td>Description:</td><td> <textarea rows='3' cols='60' input type='text' name='eg_descr'>".htmlwrap(param('eg_descr') || $gte->{DESCR} || "",1)."</textarea></tr></td>\n";
    print "<tr class='tblodd'><td>Max. assignments:</td><td> <input type='text' name='eg_max' value='".(param('eg_max') || $gte->{MAXFORM}||"")."'></tr></td>\n";
    print "<tr class='tbleven'><td>Old total assignments:</td><td> $sum</tr></td>\n";
    print "<tr class='tblodd'><td>Group created:</td><td> ".substr($gte->{WWHEN},0,16)."</tr></td>\n";
    print "<tr class='tbleven'><td>Reusable:</td><td><input type='checkbox' name='eg_public' value='1' ".((param('eg_public') || $gte->{PUBLIC}) ? " CHECKED" : "")."></td></tr>\n";
    print "</table><p/>\n";
    print "<input type='hidden' name='eg_uids' value='".join(',',keys %USERS)."'>\n";
    print "<input type='hidden' name='eg_gid' value='$grouptoedit'>\n";
    print "<input type='hidden' name='cmd' value='doeg'>\n";
    print "<table width=\"100%\"><col width=\"240\" /><col width=\"*\" /><col width=\"130\" /><tr class='tblhead'><th align=\"left\">Assigned to:</th><th align=\"left\">Amount</th><th align=\"left\">Value</th></tr>\n";
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
          print "<tr class='".(($num++)%2 ? 'tblodd' : 'tbleven')."'><td>".htmlwrap($USERS{$_}->{NAME})."</td><td><input type='text' name='eg_a$_' value='".htmlwrap(param("eg_a$_") || $forms{$_} || "")."' style=\"width:99.5%\" ></td>".($shares{$_} ? "<td>".sprintf("%.2f",calc($forms{$_}))." (".sprintf("%.2f%%",100*($shares{$_}||0)/($sums||1)).")</td>" : "<td></td>")."</tr>\n";
        }
      } else {
        if (defined($shares{$_}) && $shares{$_}>0) {
          print "<tr class='".(($num++)%2 ? 'tblodd' : 'tbleven')."'><td>Unknown</td><td><input type='hidden' name='eg_a$_' value='".htmlwrap(param("eg_a$_") || $forms{$_} || "")."' style=\"width:99.5%\" >".($forms{$_} || "")."</td>".($shares{$_} ? "<td>".sprintf("%.2f",calc($forms{$_}))." (".sprintf("%.2f%%",100*($shares{$_}||0)/($sums||1)).")</td>" : "<td></td>")."</tr>\n";
        }
      }
    }
    print "</table><p/>\n";
    print "<input type='submit' value='Edit'>\n" if ($auth_active);
    print "</form><p/>\n";
    print "<a href='$URL'>Go back</a>\n";
    output_footer;
  } elsif ($menu eq 'payment' && defined $auth_username) {
    my $tid=$path[1];
    my $sth=$dbh->prepare("SELECT T.AFU,T.AUTHOR,T.WWHEN,I.AMOUNT FROM ${prefix}TR T, ${prefix}ITEM I WHERE T.TID=? AND I.TID=? AND T.NAME IS NULL");
    $sth->execute($tid,$tid);
    my ($pfrom,$pto,$wwhen,$amount) = $sth->fetchrow_array;
    if (!defined $pfrom) {
      push @msg,['error',"Payment does not exist"];
      @path=();
      next;
    }
    if ($pfrom != $auth_uid && $pto != $auth_uid) {
      push @msg,['error',"Permission denied for viewing payment"];
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
    print "<form name='doep' action='".selfurl."' method='post'>\n";
    print "<table>\n";
    print "<input type='hidden' name='ep_id' value='$tid'>\n";
    print "<tr class='tblodd'><td>When:</td><td> ".substr($wwhen,0,16)."</td>\n";
    my $pfname=$USERS{$pfrom}->{NAME};
    my $ptname=$USERS{$pto}->{NAME};
    print "<tr class='tbleven'><td>From:</td><td> ".htmlwrap($pfname)."</td></tr>\n";
    print "<tr class='tblodd'><td>To:</td><td> ".htmlwrap($ptname)."</td></tr>\n";
    if ($pto eq $auth_uid) {
      print "<tr class='tbleven'><td>Amount:</td><td> <input type='text' name='ep_value' value='".(-$amount)."'></td></tr>\n";
      print "</table>\n";
      print "<input type='hidden' name='cmd' value='doep'>\n";
      print "<input type='submit' value='Update'>\n" if ($auth_active);
      print "<input type='submit' name='ep_delete' value='Delete' />\n";
    } else {
      print "<tr class='tbleven'><td>Amount:</td><td> ".(-$amount)."</td></tr\n";
      print "</table>\n";
    }
    print "</form><p/>\n";
    print "<a href='$URL'>Go back</a>\n";
    $sth->finish;
    output_footer;
    last;
  } elsif ($menu eq 'item' && defined $auth_username) {
    my $tid=$path[1];
    my $sth=$dbh->prepare("SELECT T.AUTHOR,T.AFG,T.AFU,I.AMOUNT,T.WWHEN,T.NAME,T.DESCR FROM ${prefix}TR T, ${prefix}ITEM I WHERE T.TID=? AND I.TID=?");
    $sth->execute($tid,$tid);
    my ($wanter,$wantedg,$wantedu,$amount,$wwhen,$name,$descr)=$sth->fetchrow_array;
    if (!defined $wanter) {
      push @msg,['error',"Item does not exist"];
      @path=();
      next;
    }
    need_user_list;
    need_group_list($wantedg) if (defined $wantedg);
    if ($auth_uid!=$wanter && defined $wantedg && !defined $GROUPS{$wantedg}) {
      push @msg,['error',"Permission denied for viewing item"];
      @path=();
      next;
    }
    if ($auth_uid!=$wanter && defined $wantedu && !defined $USERS{$wantedu}) {
      push @msg,['error',"Permission denied for viewing item"];
      @path=();
      next;
    }
    output_header;
    if ($wanter eq $auth_uid) {
      print "<h3>Edit item</h3>\n";
    } else {
      print "<h3>View item</h3>\n";
    }
    print "<form name='doew' action='".selfurl."' method='post'>\n";
    print "<input type='hidden' name='ew_id' value='$tid'>\n";
    print "<table>\n";
    print "<tr class='tblodd'><td>When:</td><td>".substr($wwhen,0,16)."</td></tr>\n";
    print "<tr class='tbleven'><td>Paid by:</td><td> ".htmlwrap($USERS{$wanter}->{NAME})."</td></tr>\n";
    print "<tr class='tblodd'><td>Paid for:</td><td> <a href='".genurl('group',$wantedg)."'>".htmlwrap($GROUPS{$wantedg}->{DNAME})."</a></td></tr>\n" if (defined $wantedg);
    print "<tr class='tblodd'><td>Paid for:</td><td> ".htmlwrap($USERS{$wantedu}->{NAME})."</a></td></tr>\n" if (defined $wantedu);
    if ($wanter eq $auth_uid) {
      print "<tr class='tbleven'><td>Name:</td><td> <input type='text' name='ew_name' value='".htmlwrap($name)."'></td></tr>\n";
      print "<tr class='tblodd'><td>Description:</td><td><textarea rows='3' cols='60' name='ew_name'>".htmlwrap($descr,1)."</textarea></td></tr>\n";
      print "<tr class='tbleven'><td>Amount:</td><td> <input type='text' name='ew_value' value='$amount'></td></tr>\n";
      print "<input type='hidden' name='cmd' value='doew'>\n";
      print "</table>\n";
      print "<input type='submit' value='Update' />" if ($auth_active);
      print "<input type='submit' name='ew_delete' value='Delete' />";
    } else {
      print "<tr class='tbleven'><td>Name:</td><td> ".htmlwrap($name)."</td></tr>\n";
      print "<tr class='tblodd'><td>Description:</td><td> ".htmlwrap($descr)."</td></tr>\n";
      print "<tr class='tbleven'><td>Amount:</td><td> $amount</td></tr>\n";
      print "</table>\n";
    }
    print "</form><br/>";
    print "<a href='$URL'>Go back</a>\n";
    $sth->finish;
    output_footer;
    last;
  } elsif ($menu eq 'bill' && defined $auth_username) {
    my $tid=$path[1];
    my $sth=$dbh->prepare("SELECT T.AUTHOR,B.DEFINITION,T.NAME,T.DESCR,T.WWHEN FROM ${prefix}TR T, ${prefix}BILL B WHERE T.TID=? AND B.TID=?");
    $sth->execute($tid,$tid);
    my ($definer,$definition,$name,$descr,$wwhen)=$sth->fetchrow_array;
    if (!defined $definer) {
      push @msg,['error',"Bill does not exist"];
      @path=();
      next;
    }
    need_user_list;
    $sth=$dbh->prepare("SELECT COUNT(*) FROM ${prefix}EF WHERE TID=? AND UID=?");
    $sth->execute($tid,$auth_uid);
    my ($cnt)=$sth->fetchrow_array;
    if ($cnt==0) {
      push @msg,['error',"Permission denied for viewing bill"];
      @path=();
      next;
    }
    output_header;
    if ($definer == $auth_uid) {
      print "<h3>Edit bill</h3>\n";
    } else {
      print "<h3>View bill</h3>\n";
    }
    print "To learn more about bills, see the <a href='".genurl('help','bill')."'>help</a> pages<p/>\n";
    print "<form name='doeb' action='".selfurl."' method='post'>\n";
    print "<input type='hidden' name='eb_id' value='$tid'>\n";
    print "<table>\n";
    print "<tr class='tblodd'><td>When:</td><td>".substr($wwhen,0,16)."</td></tr>\n";
    print "<tr class='tbleven'><td>Paid by:</td><td> ".htmlwrap($USERS{$definer}->{NAME})."</td></tr>\n";
    my ($ndef,$err,$tot,$cont,@eff)=process_bill($definition,$definer==$auth_uid ? 2 : 1);
    print "<tr class='tblodd'><td>Name:</td><td> <input type='text' name='eb_name' value='".htmlwrap($name)."'></td></tr>\n";
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
            print ((-$num)."x ");
          } elsif ($num<0 && $den>1) {
            print ((-$num)."/".($den)." of ");
          }
          if (defined $name) {
            print htmlwrap($name);
          } else {
            print sprintf("$UNIT%.2f",$amount)." item";
          }
        }
        print "]</li>\n";
      }
    }
    print "</ul></td></tr>\n";
    if ($definer eq $auth_uid) {
      print "<input type='hidden' name='cmd' value='doeb'>\n";
      print "</table>\n";
      print "<input type='submit' value='Save' />" if ($auth_active);
      print "<input type='submit' name='eb_delete' value='Delete' />";
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
    print "<div class='page-header'>\n";
    print "<h1>Edit visible people</h1>\n";
    print "</div>\n";
    print "<form class='form-horizontal form-horizontal-super-condensed' action='$URL' method='post'>\n";
    print "<input type='hidden' name='cmd' value='doev'>\n";
    my %au;
    for (sort {
      my $x=(defined($a->{VIS}) ? 0 : 1) <=> (defined($b->{VIS}) ? 0 : 1);
      return $x if ($x != 0);
      return lc($a->{NAME}) cmp lc($b->{NAME});
    } (values %USERS)) {
      if ($_->{UID}!=$auth_uid && $_->{ACTIVE}) {
        print "<div class='control-group'>\n";
        print "<label class='control-label'>".$_->{NAME}."</label> \n";
        print "<div class='controls'>\n";
        print "<input type='checkbox' name='ev_u$_->{UID}' value='1' ".(defined($_->{VIS}) ? "checked='checked'" : "").">\n";
        print "</div>\n";
        print "</div>\n";
        $au{$_->{UID}}=1;
      }
    }
    print "<input type='hidden' name='ev_uids' value='".join(',',sort keys %au)."'>\n";
    print "<div class='control-group'>\n";
    print "<div class='control-label'>\n";
    print "<input type='submit' value='Submit' class='btn btn-primary'>\n";
    print "</div>\n";
    print "</div>\n";
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
      my $sth=$dbh->prepare("SELECT AMOUNT,DESCR,WWHEN,TYP,ID FROM ${prefix}LIST WHERE UID=? ORDER BY WWHEN DESC");
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
    my $nuid=proc_req($code);
    if (defined $nuid) {
      push @msg,['info',"Creation succesful. You can log in now."];
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
      push @msg,['warn',"You do not have anyone visible. Go to <a href='".genurl('connections')."'>connections</a> to add some people."];
    }
    output_header;
    show_totals;
    show_unassigned;
    show_warn;
    show_history;
    output_footer;
  } elsif ($menu eq 'history') {
    output_header;
    show_history(1);
    output_footer;
  } elsif ($menu eq 'add') {
    output_header;
    show_form_add_pay;
    show_form_add_item;
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
      my $sth=$dbh->prepare("SELECT COUNT(*) FROM ${prefix}HTAUTH WHERE HTNAME=?");
      $sth->execute($ENV{REMOTE_USER});
      my ($cnt)=$sth->fetchrow_array;
      if ($cnt>0) {
        push @msg,['warn',"It seems you are already authenticated as ".htmlwrap($ENV{REMOTE_USER}).". Click <a href='$URL'>here</a> to log in automatically."];
        $alreadyht=1;
      }
    }
    output_header;
    print "<div class='page-header'>\n";
    print "<h1>Log in</h1>\n";
    print "</div>\n";
    print "<form class='form-horizontal form-horizontal-condensed' name='input' action='".selfurl."' method='post'>\n";
    print "<div class='control-group'>\n";
    print "<label class='control-label' for='username'>Username</label>\n";
    print "<div class='controls'>\n";
    print "<input type='text' id='username' placeholder='Username' name='username' value='".htmlwrap(param('username') || '')."'>\n";
    print "</div>\n";
    print "</div>\n";
    print "<div class='control-group'>\n";
    print "<label class='control-label' for='inputPassword'>Password</label>\n";
    print "<div class='controls'>\n";
    print "<input type='password' name='password' id='inputPassword' placeholder='Password'>\n";
    print "</div>\n";
    print "</div>\n";
    print "<div class='control-group'>\n";
    print "<div class='controls'>\n";
    print "<input type='submit' value='Log in' class='btn btn-primary'>\n";
    print "</div>\n";
    print "</div>\n";
    print "</form>\n";
    print "<div class='page-header'>\n";
    print "<h1>Create new account</h1>\n";
    print "</div>\n";
    print "<form class='form-horizontal form-horizontal-condensed' name='input' action='".selfurl."' method='post'>\n";
    print "<input type='hidden' name='cmd' value='dona' />\n";
    print "<div class='control-group'>\n";
    print "<label class='control-label' for='newFullname'  >Full Name</label>\n";
    print "<div class='controls'>\n";
    print "<input type='text' id='newFullname' name='fullname' placeholder='John Doe'>\n";
    print "</div>\n";
    print "</div>\n";
    print "<div class='control-group'>\n";
    print "<label class='control-label' for='newEmail'>E-mail address</label>\n";
    print "<div class='controls'>\n";
    print "<input type='email' id='newEmail' name='email' placeholder='john.doe&#064;something.net'>\n";
    print "<span class='help-block'>Must be unique</span>\n";
    print "</div>\n";
    print "</div>\n";
    print "<div class='control-group'>\n";
    print "<label class='control-label' for='newIBAN'>Bank account number</label>\n";
    print "<div class='controls'>\n";
    print "<input type='text' id='newIBAN' name='accnr' placeholder='BE12 3456 7890 1234'>\n";
    print "<span class='help-block'>Optional</span>\n";
    print "</div>\n";
    print "</div>\n";
    if (!$alreadyht && defined $ENV{REMOTE_USER}) {
        print "<div class='control-group'>\n";
        print "<span class='control-label'>Username</span>\n";
        print "<div class='controls'>\n";
        print " <span class='uneditable-input'>$ENV{REMOTE_USER}</span>\n";
        print "</div>";
        print "</div>";
    } else {
        print "<input type='hidden' name='dona_type' value='pw' />\n";
        print "<div class='control-group'>\n";
        print "<label class='control-label' for='newUsername'>Username</label>\n";
        print "<div class='controls'>\n";
        print "<input type='text' id='newUsername' name='uname' value='".htmlwrap(param('username') || '')."' placeholder='jdoe'>\n";
        print "<span class='help-block'>Must be unique</span>\n";
        print "</div>\n";
        print "</div>\n";
        print "<div class='control-group'>\n";
        print "<label class='control-label' for='newPassword'>Password</label>\n";
        print "<div class='controls'>\n";
        print "<input type='password' id='newPassword' name='password' placeholder='Password'>\n";
        print "<span class='help-block'>6 characters minimum</span>\n";
        print "</div>\n";
        print "</div>\n";
        print "<div class='control-group'>\n";
        print "<label class='control-label' for='newRepeatPassword'>Repeat Password</label>\n";
        print "<div class='controls'>\n";
        print "<input type='password' id='newRepeatPassword' name='password2' placeholder='Password'>\n";
        print "</div>\n";
        print "</div>\n";
    }
    print "<input type='hidden' name='cmd' value='dona' />\n";
    print "<div class='control-group'>\n";
    print "<div class='controls'>\n";
    print "<input type='submit' value='Request account' class='btn' />\n";
    print "</div>\n";
    print "</div>\n";
    print "</form>\n";
    output_footer;
  } elsif ($menu eq 'empty') {
    output_header;
    output_footer;
  } elsif ($menu eq 'error') {
    for my $err (@path[1..$#path]) {
      push @msg,['error',htmlwrap($err)];
    }
    @path=();
    next;
  } elsif ($menu eq 'help') {
    my @help=('help',@path[1..$#path]);
    my @rndnames=get_random_names 3;
    foreach my $help (@help) { $help =~ s/[^a-zA-Z0-9]//g; }
    while(1) {
      my $str="doc/".join('-',@help).".shtml";
      if (! -f $str) {
        pop @help;
      } else {
        open HELPFILE,"<$str";
        my @text = <HELPFILE>;
        close HELPFILE;
        output_header;
        print "<div class='helpnav'>";
        for (my $i=0; $i<=$#help; $i++) {
          print " / " if ($i);
          print "<a href=\"".genurl(@help[0..$i])."\">".$help[$i]."</a>";
        }
        print "</div>\n";
        print "<p/>\n";
        foreach my $text (@text) {
          $text =~ s/\$URL\((.*?)\)/pathurl($1)/eg;
          $text =~ s/\$FULLNAME/htmlwrap(defined $auth_uid ? $auth_fullname : "Your Name")/eg;
          $text =~ s/\$RNDNAME1/htmlwrap($rndnames[0])/eg;
          $text =~ s/\$RNDNAME2/htmlwrap($rndnames[1])/eg;
          $text =~ s/\$RNDNAME3/htmlwrap($rndnames[2])/eg;
          $text =~ s/\$UNIT/$UNIT/g;
          $text =~ s/\$TITLE/htmlwrap($title)/g;
          print $text;
        }
        output_footer;
        last;
      }
    }
  } else {
    @path=('error',"Unknown or inaccessible menu: $menu");
    next;
  }
  last;
}

# disconnect
$dbh->disconnect;
