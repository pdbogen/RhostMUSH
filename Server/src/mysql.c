#ifdef RHOST_MYSQL

#include <mysql.h>
#include <unistd.h>
#include <regex.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <errno.h>
#include <dirent.h>
#include <time.h>

#include "copyright.h"
#include "autoconf.h"

#include "config.h"
#include "db.h"
#include "interface.h"
#include "mudconf.h"
#include "command.h"
#include "functions.h"
#include "externs.h"
#include "match.h"
#include "flags.h"
#include "alloc.h"
#include "vattr.h"

#define MYSQL_POOL_SIZE 10

#ifdef DEBUG_MYSQL
	#define DEBUG_MYSQL(m) LOG_SIMPLE( LOG_ALWAYS, "MSQ", "DEBUG", m )
#else
	#define DEBUG_MYSQL(m)
#endif


int rhost_mysql_validate_username( char * username, char **p_buff, char ***p_bufcx );
int rhost_mysql_validate_hostname( char * hostname, char **p_buff, char ***p_bufcx );
MYSQL * rhost_mysql_connect( const char * hostname, const char * username, const char * password, const char * database, char **p_buff, char ***p_bufcx );

static char tempbuff[LBUF_SIZE];
static char tempbuff2[LBUF_SIZE];

static int ival(char *buff, char **bufcx, int result) {
   sprintf(tempbuff, "%d", result);
   safe_str(tempbuff, buff, bufcx);
   return 0;
}

typedef enum {
	unused,
	opened,
} mysql_status;

typedef struct mysql_pool_entry {
	MYSQL * connection;
	mysql_status status;
	char hostname[LBUF_SIZE],
	     username[LBUF_SIZE],
	     password[LBUF_SIZE],
	     database[LBUF_SIZE];
	time_t last_used;
} mysql_pool_entry;

static mysql_pool_entry mysql_pool[MYSQL_POOL_SIZE];

FUNCTION(local_fun_mysql_query)
{
   time_t start;
   char dbFile[LBUF_SIZE], dbFullPath[LBUF_SIZE];
   char * colPtr, *zTail;
   MYSQL * mysql_db;
   MYSQL_STMT * mysql_stmt;
   unsigned int i, rVal, firstA=1, firstB=1, argIdx, argCount;
   char colDelimit[LBUF_SIZE], rowDelimit[LBUF_SIZE];

   char *hostname, *username, *password, *database, *query;

   if ( mudstate.heavy_cpu_lockdown == 1 ) {
      safe_str("#-1 FUNCTION HAS BEEN LOCKED DOWN FOR HEAVY CPU USE.", buff, bufcx);
      return;
   }

   if( nfargs < 5 ) {
      safe_str( "#-1 FUNCTION (mysql_query) EXPECTS 5 OR MORE ARGUMENTS [RECEIVED ", buff, bufcx );
      ival( buff, bufcx, nfargs );
      safe_chr( ']', buff, bufcx );
      return;
   }

   hostname = fargs[0];
   username = fargs[1];
   password = fargs[2];
   database = fargs[3];
   query    = fargs[4];

   if ( mudstate.heavy_cpu_tmark2 > (mudstate.heavy_cpu_tmark1 + mudconf.cputimechk) ) {
      safe_str("#-1 HEAVY CPU LIMIT ON PROTECTED FUNCTION EXCEEDED", buff, bufcx);
      mudstate.chkcpu_toggle = 1;
      mudstate.heavy_cpu_recurse = mudconf.heavy_cpu_max + 1;
      if ( mudstate.heavy_cpu_tmark2 > (mudstate.heavy_cpu_tmark1 + (mudconf.cputimechk * 3)) ) {
         mudstate.heavy_cpu_lockdown = 1;
      }
      return;
   }

   mudstate.heavy_cpu_tmark2 = time(NULL);

   if( nfargs >= 6 ) {
      strncpy( colDelimit, fargs[5], LBUF_SIZE );
      if( nfargs >= 7 ) {
         strncpy( rowDelimit, fargs[6], LBUF_SIZE );
      }
   } else {
      strcpy( colDelimit, "|" );
      strcpy( rowDelimit, "^" );
   }

   // http://dev.mysql.com/doc/refman/4.1/en/user-names.html
   // http://tools.ietf.org/html/rfc1035
   // A username of 1-16 characters, optionally followed by a colon, followed by
   // a password of unlimited length, followed by an @ sign, followed by a hostname
   // A hostname is a list of .-separated labels; each label is a letter followed by up to 62 letters, digits, or hyphens

   if( !rhost_mysql_validate_hostname( hostname, &buff, &bufcx ) ) {
     return;
   }

   if( !rhost_mysql_validate_username( username, &buff, &bufcx ) ) {
     return;
   }

	DEBUG_MYSQL( "Done!" );
	DEBUG_MYSQL( "Open database.." );

	mysql_db = rhost_mysql_connect( hostname, username, password, database, &buff, &bufcx );

FUNCTION(local_fun_sql_escape) {
  int retries;
  static char bigbuff[LBUF_SIZE * 2 + 1], *s_localchr;

  if (!fargs[0] || !*fargs[0])
    return;

  memset(bigbuff, '\0', sizeof(bigbuff));

  if (!mysql_struct) {
    /* Try to reconnect. */
    retries = 0;
    while ((retries < MYSQL_RETRY_TIMES) && !mysql_struct) {
      nanosleep((struct timespec[]){{0, 900000000}}, NULL)
      sql_init(cause);
      retries++;
    }
  }

  if (!mysql_struct || (mysql_ping(mysql_struct) != 0)) {
    safe_str("#-1 NO CONNECTION", buff, bufcx);
    mysql_struct = NULL;
    return;
  }
  
  s_localchr = alloc_lbuf("local_fun_sql_escape");
  memset(s_localchr, '\0', LBUF_SIZE);
  strncpy(s_localchr, fargs[0], LBUF_SIZE-2);
  if (mysql_real_escape_string(mysql_struct, bigbuff, s_localchr, strlen(s_localchr)) < LBUF_SIZE) {
    bigbuff[LBUF_SIZE - 1] = '\0';
    bigbuff[LBUF_SIZE - 2] = '\0';
    safe_str(bigbuff, buff, bufcx);
  } else {
    safe_str("#-1 TOO LONG", buff, bufcx);
  }
  free_lbuf(s_localchr);
}

void local_mysql_init(void) {
   FUN *fp;
   char *buff, *cp, *dp;
   struct stat sb;
   unsigned int i;

	DEBUG_MYSQL( "Initializing MySQL framework" );

   static FUN mysql_fun_table[] = {
      {"MYSQL_QUERY", local_fun_mysql_query, 0, FN_VARARGS, CA_WIZARD, 0 },
      {NULL, NULL, 0, 0, 0, 0}
   };

/* Register the functions */
   buff = alloc_sbuf("init_mysql_functab");
   for (fp = mysql_fun_table ; fp->name ; fp++) {
      cp = (char *) fp->name;
      dp = buff;
      while (*cp) {
         *dp = ToLower(*cp);
         cp++;
         dp++;
      }
      *dp = '\0';
      hashadd2(buff, (int *) fp, &mudstate.func_htab, 1);
   }

   // Initialize connection pool
   for( i = 0; i < MYSQL_POOL_SIZE; i++ ) {
      mysql_pool[i].status     = unused;
      mysql_pool[i].connection = NULL;
      memset( mysql_pool[i].hostname, 0, LBUF_SIZE );
      memset( mysql_pool[i].username, 0, LBUF_SIZE );
      memset( mysql_pool[i].password, 0, LBUF_SIZE );
      mysql_pool[i].last_used = 0;
   }
}

int rhost_mysql_validate_username( char * username, char **p_buff, char ***p_bufcx ) {
	DEBUG_MYSQL( "Validating username.." );
   unsigned int n = strnlen( username, LBUF_SIZE );
   if( n > 16 || n < 1 ) {
     safe_str( "#-1 FUNCTION (mysql_query) SECOND (username) ARGUMENT MUST BE 1 TO 16 CHARACTERS [RECEIVED ", *p_buff, *p_bufcx );
     ival( *p_buff, *p_bufcx, n );
     safe_chr( ']', *p_buff, *p_bufcx );
     DEBUG_MYSQL( "Failed!" );
     return 0;
   }
   DEBUG_MYSQL( "Done!" );
   return 1;
}

int rhost_mysql_validate_hostname( char * hostname, char **p_buff, char ***p_bufcx ) {
	DEBUG_MYSQL( "Validating hostname..." );
   // Validate hostname
   regex_t validator;
   regcomp( &validator, "^(([a-z][a-z0-9-]*)(\\.[a-z][a-z0-9-]*)*)|([0-9]+\\.[0-9]+\\.[0-9]+\\.[0-9]+)$", REG_EXTENDED | REG_NOSUB | REG_ICASE );
   if( regexec( &validator, hostname, 0, NULL, 0 ) != 0 ) {
      safe_str( "#-1 FUNCTION (mysql_query) FIRST ARGUMENT (hostname) MUST BE DOMAIN NAME OR IP ADDRESS [RECEIVED ", *p_buff, *p_bufcx );
      safe_str( hostname, *p_buff, *p_bufcx );
      safe_chr( ']', *p_buff, *p_bufcx );
      regfree( &validator );
      DEBUG_MYSQL( "Failed!" );
      return 0;
   }
   regfree( &validator );
   DEBUG_MYSQL( "Done!" );
   return 1;
}

MYSQL * rhost_mysql_connect( const char * hostname, const char * username, const char * password, const char * database, char **p_buff, char ***p_bufcx ) {
   mysql_pool_entry * poolEntry = NULL;
   MYSQL * result;
   unsigned int i = 0;

   DEBUG_MYSQL( "Beginning connection process..." );

  mysql_close(mysql_struct);
  mysql_struct = NULL;
  return 0;
}
 
static int sql_init(dbref player) {
  MYSQL *result;
  
  /* If we are already connected, drop and retry the connection, in
   * case for some reason the server went away.
   */
  
  if (mysql_struct)
    sql_shutdown(player);
  
  /* Try to connect to the database host. If we have specified
   * localhost, use the Unix domain socket instead.
   */
  
  mysql_struct = mysql_init(mysql_struct);
  
  result = mysql_real_connect(mysql_struct, DB_HOST, DB_USER, DB_PASS, DB_BASE,
 			      3306, DB_SOCKET, 0);
  
  if (!result) {
    STARTLOG(LOG_PROBLEMS, "SQL", "ERR");
    log_text(unsafe_tprintf("DB connect by %s : ", player < 0 ? "SYSTEM" : Name(player)));
    log_text("Failed to connect to SQL database.");
    ENDLOG
    return -1;
  } else {
    STARTLOG(LOG_PROBLEMS, "SQL", "INF");
    log_text(unsafe_tprintf("DB connect by %s : ", player < 0 ? "SYSTEM" : Name(player)));
    log_text("Connected to SQL database.");
    ENDLOG
  }
  
  numConnectionsMade++;
  lastConnectMadeBy = player;
  numRowsRetrieved = queryCount = 0;
  return 1;
}

#define print_sep(s,b,p) \
 if (s) { \
     if (s != '\n') { \
       safe_chr(s,b,p); \
     } else { \
       safe_str((char *) "\n",b,p); \
     } \
 }
 
static int sql_query(dbref player, 
		     char *q_string, char row_delim, char field_delim, char *buff, char **bp) {
  MYSQL_RES *qres;
  MYSQL_ROW row_p;
  int num_rows, got_rows, got_fields;
  int i, j;
  int retries;
  char *tpr_buff, *tprp_buff, *s_qstr;
  
  /* If we have no connection, and we don't have auto-reconnect on
   * (or we try to auto-reconnect and we fail), this is an error
   * generating a #-1. Notify the player, too, and set the return code.
   */
  
  if (!mysql_struct) {
    /* Try to reconnect. */
    retries = 0;
    while ((retries < MYSQL_RETRY_TIMES) && !mysql_struct) {
      nanosleep((struct timespec[]){{0, 900000000}}, NULL)
      sql_init(player);
      retries++;
    }
  }
  if (!mysql_struct || (mysql_ping(mysql_struct) != 0)) {
    notify(player, "No SQL database connection.");
    if (buff)
      safe_str("#-1", buff, bp);
    sql_shutdown(player);
    return -1;
  }

  if (!q_string || !*q_string)
    return 0;
  
  /* Send the query. */
  
  alarm_msec(5);
  s_qstr = alloc_lbuf("tmp_q_string");
  memset(s_qstr, '\0', LBUF_SIZE);
  strncpy(s_qstr, q_string, LBUF_SIZE - 2);
  got_rows = mysql_real_query(mysql_struct, s_qstr, strlen(s_qstr));
  if ( mudstate.alarm_triggered ) {
     notify(player, "The SQL engine forced a failure on a timeout.");
     sql_shutdown(player);
     mudstate.alarm_triggered = 0;
     alarm_msec(next_timer());
     free_lbuf(s_qstr);
     return 0;
  }
  free_lbuf(s_qstr);
  mudstate.alarm_triggered = 0;
  alarm_msec(next_timer());


  if ((got_rows) && (mysql_errno(mysql_struct) == CR_SERVER_GONE_ERROR)) {
    
    /* We got this error because the server died unexpectedly
     * and it shouldn't have. Try repeatedly to reconnect before
     * giving up and failing. This induces a few seconds of lag,
     * depending on number of retries; we put in the sleep() here
     * to see if waiting a little bit helps.
     */
    
    retries = 0;
    sql_shutdown(player);
    
    while ((retries < MYSQL_RETRY_TIMES) && (!mysql_struct)) {
      nanosleep((struct timespec[]){{0, 900000000}}, NULL)
      sql_init(player);
      retries++;
    }
    
    if (mysql_struct) {
      alarm_msec(5);
      s_qstr = alloc_lbuf("tmp_q_string");
      memset(s_qstr, '\0', LBUF_SIZE);
      strncpy(s_qstr, q_string, LBUF_SIZE - 2);
      got_rows = mysql_real_query(mysql_struct, s_qstr, strlen(s_qstr));
      if ( mudstate.alarm_triggered ) {
         notify(player, "The SQL engine forced a failure on a timeout.");
         sql_shutdown(player);
         mudstate.alarm_triggered = 0;
         alarm_msec(next_timer());
         free_lbuf(s_qstr);
         return 0;
      }
      free_lbuf(s_qstr);
      mudstate.alarm_triggered = 0;
      alarm_msec(next_timer());
    }
  }
  if (got_rows) {
    notify(player, mysql_error(mysql_struct));
    if (buff)
      safe_str("#-1", buff, bp);
    return -1;
  }
  
  /* A number of affected rows greater than 0 means it wasnt a SELECT */
  
  tprp_buff = tpr_buff = alloc_lbuf("sql_query");

  num_rows = mysql_affected_rows(mysql_struct);
  if (num_rows > 0) {
    tprp_buff = tpr_buff;
    notify(player, safe_tprintf(tpr_buff, &tprp_buff, "SQL query touched %d %s.",
			   num_rows, (num_rows == 1) ? "row" : "rows"));
    free_lbuf(tpr_buff);
    return 0;
  } else if (num_rows == 0) {
    free_lbuf(tpr_buff);
    return 0;
  }
  
  /* Check to make sure we got rows back. */
  
  qres = mysql_store_result(mysql_struct);
  got_rows = mysql_num_rows(qres);
  if (got_rows == 0) {
    mysql_free_result(qres);
    free_lbuf(tpr_buff);
    return 0;
  }

  /* Construct properly-delimited data. */
  
  if (buff) {
    for (i = 0; i < got_rows; i++) {
      if (i > 0) {
        if ( row_delim != '\0' ) {
	   print_sep(row_delim, buff, bp);
        } else {
	   print_sep(' ', buff, bp);
        }
      }
      row_p = mysql_fetch_row(qres);
      if (row_p) {
	got_fields = mysql_num_fields(qres);
	for (j = 0; j < got_fields; j++) {
	  if (j > 0) {
             if ( field_delim != '\0' ) {
	       print_sep(field_delim, buff, bp);
             } else {
	       print_sep(' ', buff, bp);
             }
	  }
	  if (row_p[j] && *row_p[j]) {
	    safe_str(row_p[j], buff, bp);
          } else if ( !row_p[j] ) {
            break;
          }
	}
      }
    }
  } else {
    for (i = 0; i < got_rows; i++) {
      row_p = mysql_fetch_row(qres);
      if (row_p) {
	got_fields = mysql_num_fields(qres);
	for (j = 0; j < got_fields; j++) {
          tprp_buff = tpr_buff;
	  if (row_p[j] && *row_p[j]) {
	    notify(player, safe_tprintf(tpr_buff, &tprp_buff, "Row %d, Field %d: %.3900s",
				   i + 1, j + 1, row_p[j]));
          } else if ( !row_p[j] ) {
            break;
         }
      }
   }

   // FIXME: Free oldest slot

   // Connect
   if( poolEntry == NULL ) {
      safe_str( "#-1 FUNCTION (mysql_query) FAILED TO LOCATE AVAILABLE CONNECTION POOL SLOT. THIS SHOULD NOT HAPPEN.", *p_buff, *p_bufcx );
      return NULL;
   }

   poolEntry->connection = mysql_init(NULL);

   if( poolEntry->connection == NULL ) {
      safe_str( "#-1 FUNCTION (mysql_query) FAILED TO INITIALIZE MYSQL CONNECTION. THIS IS A MAJOR PROBLEM.", *p_buff, *p_bufcx );
      return NULL;
   }

   strncpy( poolEntry->hostname, hostname, LBUF_SIZE );
   strncpy( poolEntry->password, password, LBUF_SIZE );
   strncpy( poolEntry->username, username, LBUF_SIZE );
   strncpy( poolEntry->database, database, LBUF_SIZE );

   result = mysql_real_connect( poolEntry->connection,
                                poolEntry->hostname,
                                poolEntry->username,
                                poolEntry->password,
                                poolEntry->database,
                                0, // FIXME: port
                                NULL,
                                CLIENT_MULTI_STATEMENTS
   );

   if( result == NULL ) {
     snprintf( tempbuff, LBUF_SIZE, "#-1 FUNCTION (mysql_query) FAILED TO CONNECT: %s", mysql_error( poolEntry->connection ) );
     safe_str( tempbuff, *p_buff, *p_bufcx );
     DEBUG_MYSQL( "Failed to connect" );
     DEBUG_MYSQL( (char*) mysql_error( poolEntry->connection ) );
     mysql_close( poolEntry->connection );
     return NULL;
   }

   poolEntry->status = opened;
   DEBUG_MYSQL( "Connected!" );
   return poolEntry->connection;
}

#endif // RHOST_MYSQL
