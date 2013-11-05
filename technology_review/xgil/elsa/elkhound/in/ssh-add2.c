/*

ssh-add.c

  Authors:
        Tatu Ylonen <ylo@ssh.com>
        Markku-Juhani Saarinen <mjos@ssh.com>
        Timo J. Rinne <tri@ssh.com>
        Sami Lehtinen <sjl@ssh.com>

  Copyright (C) 1997-2000 SSH Communications Security Corp, Helsinki, Finland
  All rights reserved.

  Adds an identity to the authentication server, or removes an identity.

*/

/*
 * $Id: ssh-add2.c,v 1.1 2002/08/11 00:17:28 scott Exp $
 * $Log: ssh-add2.c,v $
 * Revision 1.1  2002/08/11 00:17:28  scott
 * removed some obsolete files, moved more input to in/
 *
 * Revision 1.1  2000/07/28 08:39:56  scott
 * everything works and I can parse ssh-add2
 * I am now working on improving the performance
 *
 * $EndLog$
 */

#include "sshincludes.h"
#include "sshcrypt.h"
#include "sshtimeouts.h"
#include "sshuserfiles.h"
#include "sshagent.h"
#include "sshuser.h"
#include "readpass.h"
#include "sshuserfiles.h"
#include "ssheloop.h"
#include "sshgetopt.h"
#include "sshmiscstring.h"
#ifdef WITH_PGP
#include "sshbuffer.h"
#include "sshfilebuffer.h"
#include "sshpgp.h"
#include "ssh2pgp.h"
#include "ssh2pubkeyencode.h"
#include "ssh1keydecode.h"
#endif /* WITH_PGP */
#include "sshdsprintf.h"

#define SSH_DEBUG_MODULE "SshAdd"

#ifdef HAVE_LIBWRAP
int allow_severity = SSH_LOG_INFORMATIONAL;
int deny_severity = SSH_LOG_WARNING;
#endif /* HAVE_LIBWRAP */

#define EXIT_STATUS_OK          0
#define EXIT_STATUS_NOAGENT     1
#define EXIT_STATUS_BADPASS     2
#define EXIT_STATUS_NOFILE      3
#define EXIT_STATUS_NOIDENTITY  4
#define EXIT_STATUS_ERROR       5

typedef enum 
{ 
  LIST, 
  ADD, 
  ADD_URL,
  DELETE,
  DELETE_URL,
  DELETE_ALL, 
  LOCK, 
  UNLOCK 
} SshAgentAction;

#ifdef WITH_PGP
typedef enum
{
  PGP_KEY_NONE = 0,
  PGP_KEY_NAME,
  PGP_KEY_FINGERPRINT,
  PGP_KEY_ID
} SshAgentPgpKeyMode;
#endif /* WITH_PGP */

char *av0;

/* Files to add/delete from agent. */
char **files;
int num_files;
SshAgentAction action;
#ifdef WITH_PGP
SshAgentPgpKeyMode pgp_mode = PGP_KEY_NONE;
char *pgp_keyring;
#endif /* WITH_PGP */

/* Possible attributes */
SshUInt32 path_limit = 0xffffffff;
char *path_constraint = NULL;
Boolean forbid_compat = FALSE;
SshTime key_timeout = 0;
Boolean have_attrs = FALSE;
SshUInt32 use_limit = 0xffffffff;

/* Force to read passphrases from stdin. */
int use_stdin = FALSE;

/* Information about the current user. */
SshUser user;

void agent_completion(SshAgentError result, void *context);

void add_file(SshAgent agent, const char *filename)
{
  SshPrivateKey key = NULL;
  char *saved_comment, *comment = NULL, *pass;
  int query_cnt;
  unsigned char *certs = NULL;
  size_t certs_len;
  char privname[500], pubname[500];
  unsigned long magic;
  struct stat st;

  if (action == ADD_URL)
    {
      printf("Adding URL identity: %s\n", filename);
      snprintf(privname, sizeof(privname), "%s", filename);
      if (have_attrs)
        ssh_agent_add_with_attrs(agent, NULL, NULL, 0, privname,
                                 path_limit, path_constraint, use_limit,
                                 forbid_compat, key_timeout,
                                 agent_completion, (void *)agent);
      else
        ssh_agent_add(agent, NULL, NULL, 0, privname,
                      agent_completion, (void *)agent);
      return;
    }
  else if (action == DELETE_URL)
    {
      printf("Deleting URL identity: %s\n", filename);
      snprintf(privname, sizeof(privname), "%s", filename);
      ssh_agent_delete(agent, NULL, 0, privname,
                       agent_completion, (void *)agent);
      return;
    }
#ifdef WITH_PGP
  if (pgp_mode == PGP_KEY_NONE)
#endif /* WITH_PGP */
    {
      /* Construct the names of the public and private key files. */
      if (strlen(filename) > 4 &&
          strcmp(filename + strlen(filename) - 4, ".pub") == 0)
        {
          snprintf(pubname, sizeof(pubname), "%s", filename);
          snprintf(privname, sizeof(privname), "%s", filename);
          privname[strlen(privname) - 4] = '\0';
        }
      else
        {
          snprintf(pubname, sizeof(pubname), "%s.pub", filename);
          snprintf(privname, sizeof(privname), "%s", filename);
        }
    
      if (action == ADD)
        printf("Adding identity: %s\n", pubname);
      else if (action == DELETE)
        printf("Deleting identity: %s\n", pubname);
    
      if (stat(pubname, &st) < 0)
        {
          printf("Public key file %s does not exist.\n", pubname);
          (*agent_completion)(SSH_AGENT_ERROR_OK, (void *)agent);
          return;
        }
    
      if (stat(privname, &st) < 0)
        {
          printf("Private key file %s does not exist.\n", privname);
          (*agent_completion)(SSH_AGENT_ERROR_OK, (void *)agent);
          return;
        }
    
      /* Read the public key blob. */
      magic = ssh2_key_blob_read(user, 
                                 pubname,
                                 TRUE,
                                 &saved_comment,
                                 &certs, 
                                 &certs_len,
                                 NULL);
      if (magic != SSH_KEY_MAGIC_PUBLIC)
        {
          printf("Bad public key file %s\n", pubname);
          ssh_xfree(certs);
          (*agent_completion)(SSH_AGENT_ERROR_OK, (void *)agent);
          return;
        }
    
      if (action == ADD)
        {
          /* Loop until we manage to load the file, or a maximum number of
             attempts have been made.  First try with an empty passphrase. */
          pass = ssh_xstrdup("");
          query_cnt = 0;
          while ((key = ssh_privkey_read(user, 
                                         privname,
                                         pass, 
                                         &comment, 
                                         NULL)) == NULL)
            {
              char buf[1024];
              FILE *f;
            
              /* Free the old passphrase. */
              memset(pass, 0, strlen(pass));
              ssh_xfree(pass);
            
              query_cnt++;
              if (query_cnt > 5)
                {
                  fprintf(stderr,
                          "You don't seem to know the correct passphrase.\n");
                  exit(EXIT_STATUS_BADPASS);
                }
            
              /* Ask for a passphrase. */
              if (!use_stdin && getenv("DISPLAY") && !isatty(fileno(stdin)))
                {
                  snprintf(buf, sizeof(buf),
                           "ssh-askpass2 '%sEnter passphrase for %.100s'", 
                           ((query_cnt <= 1) ? 
                            "" : 
                            "You entered wrong passphrase.  "), 
                           saved_comment);
                  f = popen(buf, "r");
                  if (!fgets(buf, sizeof(buf), f))
                    {
                      pclose(f);
                      ssh_xfree(saved_comment);
                      exit(EXIT_STATUS_BADPASS);
                    }
                  pclose(f);
                  if (strchr(buf, '\n'))
                    *strchr(buf, '\n') = 0;
                  pass = ssh_xstrdup(buf);
                }
              else
                {
                  if (query_cnt <= 1)
                    {
                      if ((strcmp(privname, saved_comment) == 0) ||
                          (((strlen(privname) + 4) == strlen(saved_comment)) &&
                           (strncmp(privname, 
                                    saved_comment, 
                                    strlen(privname)) == 0)))
                        {
                          printf("Need passphrase for %s.\n", 
                                 privname);
                        }
                      else
                        {
                          printf("Need passphrase for %s (%s).\n", 
                                 privname, saved_comment);
                        }
                    }
                  else
                    {
                      printf("Bad passphrase.\n");
                    }
                  pass = ssh_read_passphrase("Enter passphrase: ", use_stdin);
                  if (pass == NULL || strcmp(pass, "") == 0)
                    {
                      ssh_xfree(saved_comment);
                      ssh_xfree(pass);
                      exit(EXIT_STATUS_BADPASS);
                    }
                }
            }
          memset(pass, 0, strlen(pass));
          ssh_xfree(pass);
          ssh_xfree(saved_comment);
          /* Construct a comment for the key by combining file name and
             comment in the file. */
          if ((saved_comment = strrchr(privname, '/')) != NULL)
            saved_comment++;
          else
            saved_comment = privname;
          saved_comment = ssh_string_concat_3(saved_comment, ": ", comment);
        }
      else
        {
          /* Construct a comment for the key by combining file name and
             comment in the file. */
          if ((saved_comment = strrchr(privname, '/')) != NULL)
            saved_comment++;
          else
            saved_comment = privname;
          if (comment)
            saved_comment = ssh_string_concat_3(saved_comment, ": ", comment);
          else
            saved_comment = ssh_xstrdup(saved_comment);
        }
    
      if (action == ADD)
        {
          /* Send the key to the authentication agent. */
          if (have_attrs)
            ssh_agent_add_with_attrs(agent, key, certs, certs_len, 
                                     saved_comment, path_limit, 
                                     path_constraint, use_limit,
                                     forbid_compat, key_timeout,
                                     agent_completion, (void *)agent);
          else
            ssh_agent_add(agent, key, certs, certs_len, saved_comment,
                          agent_completion, (void *)agent);
          ssh_private_key_free(key);
        }
      else if (action == DELETE)
        {
          ssh_agent_delete(agent, certs, certs_len, saved_comment,
                           agent_completion, (void *)agent);
        }
      ssh_xfree(saved_comment);
    }
#ifdef WITH_PGP
  else
    {
      unsigned char *blob, *public_blob;
      size_t blob_len, public_blob_len;
      Boolean found = FALSE;
      unsigned long id;
      char *endptr;
      SshPgpSecretKey pgp_key;
      SshPrivateKey key;
      char buf[1024];
      FILE *f;

      comment = NULL;
      switch (pgp_mode)
        {
        case PGP_KEY_NAME:
          found = ssh2_find_pgp_secret_key_with_name(user,
                                                     pgp_keyring,
                                                     filename,
                                                     &blob,
                                                     &blob_len,
                                                     &comment);
          break;
          
        case PGP_KEY_FINGERPRINT:
          found = ssh2_find_pgp_secret_key_with_fingerprint(user,
                                                            pgp_keyring,
                                                            filename,
                                                            &blob,
                                                            &blob_len,
                                                            &comment);
          break;
          
        case PGP_KEY_ID:
          id = strtoul(filename, &endptr, 0);
          if ((*filename != '\0') && (*endptr == '\0'))
            {
              found = ssh2_find_pgp_secret_key_with_id(user,
                                                       pgp_keyring,
                                                       id,
                                                       &blob,
                                                       &blob_len,
                                                       &comment);
            }
          else
            {
              fprintf(stderr, "%s: invalid pgp key id \"%s\".\n", 
                      av0, filename);
              found = FALSE;
            }
          break;
          
        default:
          ssh_fatal("internal error");
        }
      if (! found)
        {
          fprintf(stderr, "%s: pgp key \"%s\" not found.\n", 
                  av0, filename);
          (*agent_completion)(SSH_AGENT_ERROR_OK, (void *)agent);
          return;
        }
      if (ssh_pgp_secret_key_decode(blob, blob_len, &pgp_key) == 0)
        {
          fprintf(stderr, "%s: unable to decode pgp key \"%s\".\n", 
                  av0, filename);
          memset(blob, 'F', blob_len);
          ssh_xfree(blob);
          (*agent_completion)(SSH_AGENT_ERROR_OK, (void *)agent);
          return;
        }

      if ((public_blob_len = ssh_encode_pubkeyblob(pgp_key->public_key->key,
                                                   &public_blob)) == 0)
        {
          fprintf(stderr, "%s: unable to encode pgp key \"%s\".\n", 
                  av0, filename);
          ssh_pgp_secret_key_free(pgp_key);
          memset(blob, 'F', blob_len);
          ssh_xfree(blob);
          (*agent_completion)(SSH_AGENT_ERROR_OK, (void *)agent);
          return;
        }
      if (action == ADD)
        {
          query_cnt = 0;
          while ((pgp_key->key == NULL) &&
                 (pgp_key->decryption_failed == TRUE))
            {
              query_cnt++;
              if (query_cnt > 5)
                {
                  fprintf(stderr,
                          "You don't seem to know the correct passphrase.\n");
                  exit(EXIT_STATUS_BADPASS);
                }
              /* Ask for a passphrase. */
              if (!use_stdin && getenv("DISPLAY") && !isatty(fileno(stdin)))
                {
                  snprintf(buf, sizeof(buf),
                           "ssh-askpass2 '%sEnter passphrase for \"%.100s\"'", 
                           ((query_cnt <= 1) ? 
                            "" : 
                            "You entered wrong passphrase.  "), 
                           comment);
                  f = popen(buf, "r");
                  if (!fgets(buf, sizeof(buf), f))
                    {
                      pclose(f);
                      fprintf(stderr, "No passphrase.\n");
                      exit(EXIT_STATUS_BADPASS);
                    }
                  pclose(f);
                  if (strchr(buf, '\n'))
                    *strchr(buf, '\n') = 0;
                  pass = ssh_xstrdup(buf);
                }
              else
                {
                  if (query_cnt <= 1)
                    printf("Need passphrase for \"%s\".\n", comment);
                  else
                    printf("Bad passphrase.\n");
                  pass = ssh_read_passphrase("Enter passphrase: ", use_stdin);
                  if (pass == NULL || strcmp(pass, "") == 0)
                    {
                      ssh_xfree(pass);
                      fprintf(stderr, "No passphrase.\n");
                      exit(EXIT_STATUS_BADPASS);
                    }
                }
              ssh_pgp_secret_key_free(pgp_key);
              if (ssh_pgp_secret_key_decode_with_passphrase(blob, 
                                                            blob_len, 
                                                            pass,
                                                            &pgp_key) == 0)
                {
                  memset(pass, 0, strlen(pass));
                  ssh_xfree(pass);
                  fprintf(stderr, "%s: unable to decode pgp key \"%s\".\n", 
                          av0, filename);
                  memset(blob, 'F', blob_len);
                  ssh_xfree(blob);
                  ssh_xfree(public_blob);
                  (*agent_completion)(SSH_AGENT_ERROR_OK, (void *)agent);
                  return;
                }
              memset(pass, 0, strlen(pass));
              ssh_xfree(pass);
            }
          if (pgp_key->key == NULL)
            {
              fprintf(stderr, "%s: unable to decode pgp key \"%s\".\n", 
                      av0, filename);
              ssh_xfree(public_blob);
              ssh_pgp_secret_key_free(pgp_key);
              (*agent_completion)(SSH_AGENT_ERROR_OK, (void *)agent);
              return;
            }
          memset(blob, 'F', blob_len);
          ssh_xfree(blob);
          if (ssh_private_key_copy(pgp_key->key, &key) != SSH_CRYPTO_OK)
            {
              fprintf(stderr, "%s: unable to export pgp key \"%s\".\n", 
                      av0, filename);
              ssh_pgp_secret_key_free(pgp_key);
              (*agent_completion)(SSH_AGENT_ERROR_OK, (void *)agent);
              return;
            }
          ssh_pgp_secret_key_free(pgp_key);
          if (have_attrs)
            ssh_agent_add_with_attrs(agent, key, 
                                     public_blob, public_blob_len, 
                                     comment, path_limit, 
                                     path_constraint, use_limit,
                                     forbid_compat, key_timeout,
                                     agent_completion, (void *)agent);
          else
            ssh_agent_add(agent, key, 
                          public_blob, public_blob_len, comment, 
                          agent_completion, (void *)agent);
          ssh_xfree(comment);
          ssh_xfree(public_blob);
          ssh_private_key_free(key);
          return;
        }
      else if (action == DELETE)
        {
          ssh_agent_delete(agent, 
                           public_blob, 
                           public_blob_len, 
                           filename,
                           agent_completion,
                           (void *)agent);
          ssh_pgp_secret_key_free(pgp_key);
          memset(blob, 'F', blob_len);
          ssh_xfree(blob);
          ssh_xfree(public_blob);
          return;
        }
    }
#endif /* WITH_PGP */
}

void agent_completion(SshAgentError result, void *context)
{
  SshAgent agent = (SshAgent)context;

  switch (result)
    {
    case SSH_AGENT_ERROR_OK:
      break;

    case SSH_AGENT_ERROR_TIMEOUT:
      fprintf(stderr, "Authentication agent timed out.\n");
      exit(EXIT_STATUS_NOAGENT);
      
    case SSH_AGENT_ERROR_KEY_NOT_FOUND:
      fprintf(stderr,
              "Requested key not in possession of authentication agent.\n");
      exit(EXIT_STATUS_NOIDENTITY);
      
    case SSH_AGENT_ERROR_DECRYPT_FAILED:
      fprintf(stderr, "Decryption failed.\n");
      exit(EXIT_STATUS_ERROR);
      
    case SSH_AGENT_ERROR_SIZE_ERROR:
      fprintf(stderr, "Argument size error.\n");
      exit(EXIT_STATUS_ERROR);
      
    case SSH_AGENT_ERROR_KEY_NOT_SUITABLE:
      fprintf(stderr, 
              "The specified key is not suitable for the operation.\n");
      exit(EXIT_STATUS_ERROR);
      
    case SSH_AGENT_ERROR_DENIED:
      fprintf(stderr, "The requested operation was denied.\n");
      exit(EXIT_STATUS_ERROR);
      
    case SSH_AGENT_ERROR_FAILURE:
      fprintf(stderr, "The requested operation failed.\n");
      exit(EXIT_STATUS_ERROR);
      
    case SSH_AGENT_ERROR_UNSUPPORTED_OP:
      fprintf(stderr, "The requested operation is not supported.\n");
      exit(EXIT_STATUS_ERROR);
      
    case SSH_AGENT_ERROR_BUSY:
      fprintf(stderr, "The authentication agent is busy.\n");
      exit(EXIT_STATUS_ERROR);
      
    default:
      fprintf(stderr, "Authentication agent failed with error %d\n",
              (int)result);
      exit(EXIT_STATUS_ERROR);
    }

  /* The last operation was successful.  Check if there is more work to do. */
  if (num_files <= 0)
    {
      /* All operations performed. */
      exit(EXIT_STATUS_OK);
    }

  /* Add any files listed. */
  num_files--;
  add_file(agent, *files++);
  /* A callback should already have been scheduled to occur at some point. */
}

void agent_list_callback(SshAgentError error, unsigned int num_keys,
                             SshAgentKeyInfo keys, void *context)
{
  SshAgent agent = (SshAgent)context;
  int i;

  if (error != SSH_AGENT_ERROR_OK)
    {
      agent_completion(error, (void *)agent);
      ssh_fatal("agent_list_callback: agent_completion returned after error");
    }

  if (num_keys == 0)
    printf("The authorization agent has no keys.\n");
  else
    {
      if (num_keys == 1)
        printf("The authorization agent has one key:\n");
      else
        printf("The authorization agent has %d keys:\n", num_keys);
      for (i = 0; i < num_keys; i++)
        printf("%s\n", keys[i].description);
    }
  agent_completion(SSH_AGENT_ERROR_OK, (void *)agent);
}

void agent_open_callback(SshAgent agent, void *context)
{
  char buf[1024];
  FILE *f;
  char *password, *password_vrfy;

  if (!agent)
    {
      fprintf(stderr,
        "Failed to connect to authentication agent - agent not running?\n");
      exit(EXIT_STATUS_NOAGENT);
    }

  switch (action)
    {
    case DELETE_ALL:
      fprintf(stderr, "Deleting all identities.\n");
      ssh_agent_delete_all(agent, agent_completion, (void *)agent);
      break;
      
    case LIST:
      fprintf(stderr, "Listing identities.\n");
      ssh_agent_list(agent, agent_list_callback, (void *)agent);
      break;
      
    case LOCK:
      if (!use_stdin && getenv("DISPLAY") && !isatty(fileno(stdin)))
        {
          snprintf(buf, sizeof (buf),
                   "ssh-askpass2 'Enter lock passphrase'");
          f = popen(buf, "r");
          if (! fgets(buf, sizeof (buf), f))
            {
              pclose(f);
              exit(EXIT_STATUS_BADPASS);
            }
          pclose(f);
          if (strchr(buf, '\n'))
            *strchr(buf, '\n') = 0;
          password = ssh_xstrdup(buf);
        }
      else
        {
          password = ssh_read_passphrase("Enter lock password: ", use_stdin);
          if (password == NULL)
            {
              fprintf(stderr, "Unable to read password.\n");
                exit(EXIT_STATUS_BADPASS);
            }
          password_vrfy = ssh_read_passphrase("Again: ", use_stdin);
          if (password_vrfy == NULL)
            {
              fprintf(stderr, "Unable to read password.\n");
              exit(EXIT_STATUS_BADPASS);
            }
          if (strcmp(password, password_vrfy) != 0)
            {
              fprintf(stderr, "Passwords don't match.\n");
              exit(EXIT_STATUS_BADPASS);
            }
        }
      ssh_agent_lock(agent, password, agent_completion, (void *)agent);
      break;

    case UNLOCK:
      if (!use_stdin && getenv("DISPLAY") && !isatty(fileno(stdin)))
        {
          snprintf(buf, sizeof (buf),
                   "ssh-askpass2 'Enter unlock passphrase'");
          f = popen(buf, "r");
          if (! fgets(buf, sizeof (buf), f))
            {
              pclose(f);
              exit(EXIT_STATUS_BADPASS);
            }
          pclose(f);
          if (strchr(buf, '\n'))
            *strchr(buf, '\n') = 0;
          password = ssh_xstrdup(buf);
        }
      else
        {
          password = ssh_read_passphrase("Enter lock password: ", use_stdin);
          if (password == NULL)
            {
              exit(EXIT_STATUS_BADPASS);
            }
        }
      ssh_agent_unlock(agent, password, agent_completion, (void *)agent);
      break;

    case DELETE:
    case DELETE_URL:
    case ADD:
    case ADD_URL:
      /* Let the completion do all the work. */
      agent_completion(SSH_AGENT_ERROR_OK, (void *)agent);
      break;

    default:
      ssh_fatal("agent_open_callback: bad action %d\n", (int)action);
    }
}

void usage(void);
void usage()
{
  fprintf(stderr, "Usage: %s [-l] [-d] [-D] [-p] [-t key_exp] [-f hop_limit] [-1] [files...]\n", av0);
}

/* This is the main program for the agent. */

int main(int ac, char **av)
{
  int opt, i;
  DIR *ssh2dir = NULL;
  char *ssh2dirname;
  Boolean dynamic_array = FALSE;
  struct dirent * cand;

  /* Save program name. */
  if (strchr(av[0], '/'))
    av0 = strrchr(av[0], '/') + 1;
  else
    av0 = av[0];

  user = ssh_user_initialize(NULL, FALSE);

#ifdef WITH_PGP
  pgp_keyring = ssh_xstrdup(SSH_PGP_SECRET_KEY_FILE);
#endif /* WITH_PGP */

  action = ADD;
  while ((opt = ssh_getopt(ac, av, "ldDput:f:F:1LUNPI", NULL)) != EOF)
    {
      if (!ssh_optval)
        {
          usage();
          exit(EXIT_STATUS_ERROR);
        }
      switch (opt)
        {
        case 'N':
#ifdef WITH_PGP
          pgp_mode = PGP_KEY_NAME;
#else /* WITH_PGP */
          fprintf(stderr, "%s: PGP keys not supported.\n", av0);
          exit(EXIT_STATUS_ERROR);
#endif /* WITH_PGP */
          break;

        case 'P':
#ifdef WITH_PGP
          pgp_mode = PGP_KEY_FINGERPRINT;
#else /* WITH_PGP */
          fprintf(stderr, "%s: PGP keys not supported.\n", av0);
          exit(EXIT_STATUS_ERROR);
#endif /* WITH_PGP */
          break;

        case 'I':
#ifdef WITH_PGP
          pgp_mode = PGP_KEY_ID;
#else /* WITH_PGP */
          fprintf(stderr, "%s: PGP keys not supported.\n", av0);
          exit(EXIT_STATUS_ERROR);
#endif /* WITH_PGP */
          break;

        case 'R':
#ifdef WITH_PGP
          ssh_xfree(pgp_keyring);
          pgp_keyring = ssh_xstrdup(ssh_optarg);
#else /* WITH_PGP */
          fprintf(stderr, "%s: PGP keys not supported.\n", av0);
          exit(EXIT_STATUS_ERROR);
#endif /* WITH_PGP */
          break;

        case 'l':
          action = LIST;
          break;

        case 'p':
          use_stdin = TRUE;
          break;

        case 'd':
          if (action == ADD_URL)
            action = DELETE_URL;
          else
            action = DELETE;
          break;

        case 'D':
          action = DELETE_ALL;
          break;

        case 't':
          if (ssh_optargnum)
            {
              key_timeout = (SshTime)(ssh_optargval * 60);
            }
          else
            {
              usage();
              exit(EXIT_STATUS_ERROR);
            }
          have_attrs = TRUE;
          break;

        case 'f':
          if (ssh_optargnum)
            {
              path_limit = (SshUInt32)ssh_optargval;
            }
          else
            {
              usage();
              exit(EXIT_STATUS_ERROR);
            }
          have_attrs = TRUE;
          break;

        case 'F':
          path_constraint = ssh_xstrdup(ssh_optarg);
          have_attrs = TRUE;
          break;

        case '1':
          forbid_compat = TRUE;
          have_attrs = TRUE;
          break;

        case 'u':
          if (action == DELETE)
            action = DELETE_URL;
          else
            action = ADD_URL;
          break;

        case 'L':
          action = LOCK;
          break;

        case 'U':
          action = UNLOCK;
          break;

        default:
          usage();
          exit(EXIT_STATUS_ERROR);
        }
    }

#ifdef WITH_PGP
  if (pgp_keyring[0] != '/')
    {
      char buf[1024];
      snprintf(buf, sizeof (buf), "%s/%s/%s", 
               ssh_user_dir(user), 
               SSH_USER_DIR,
               pgp_keyring);
      ssh_xfree(pgp_keyring);
      pgp_keyring = ssh_xstrdup(buf);
    }
#endif /* WITH_PGP */

  files = &av[ssh_optind];
  num_files = ac - ssh_optind;

  /* Fetch default from ~/.ssh2/id_* (the first that we happen to get) */

#define ID_PREFIX "id"
  
  if (num_files == 0 && action != LIST && action != DELETE_ALL &&
      action != LOCK && action != UNLOCK)
    {
#ifdef WITH_PGP
      if (pgp_mode != PGP_KEY_NONE)
        {
          fprintf(stderr, "%s: Nothing to do!\n",  av0);
          exit(EXIT_STATUS_ERROR);
        }
#endif /* WITH_PGP */
      ssh_dsprintf(&ssh2dirname, "%s/%s", ssh_user_dir(user), SSH_USER_DIR);
      ssh2dir = opendir(ssh2dirname);

      if (!ssh2dir)
        {
          fprintf(stderr, "%s: Can't open directory \"%s\"", av0, ssh2dirname);
          exit(EXIT_STATUS_ERROR);
        }
          
      while ((cand = readdir(ssh2dir)) != NULL)
        {
          if ((strlen(cand->d_name) > strlen(ID_PREFIX)) &&
              (strncmp(cand->d_name, ID_PREFIX, strlen(ID_PREFIX)) == 0) &&
              ((strlen(cand->d_name) < 4) ||
               (strcmp(cand->d_name + strlen(cand->d_name) - 4,
                       ".pub") != 0)) &&
              ((((cand->d_name)[strlen(ID_PREFIX)]) == '_') ||
               (((cand->d_name)[strlen(ID_PREFIX)]) == '-') ||
               (((cand->d_name)[strlen(ID_PREFIX)]) == '.') ||
               (((cand->d_name)[strlen(ID_PREFIX)]) == '(') ||
               (((cand->d_name)[strlen(ID_PREFIX)]) == '[') ||
               (((cand->d_name)[strlen(ID_PREFIX)]) == '<') ||
               (((cand->d_name)[strlen(ID_PREFIX)]) == '>')))
            {
              files = ssh_xcalloc(2, sizeof(char *));
              ssh_dsprintf(&files[0], "%s/%s", ssh2dirname, cand->d_name);
              ssh_xfree(ssh2dirname);
              num_files++;
              dynamic_array = TRUE;
              break;
            }
        }
      (void)closedir(ssh2dir);
    }
  
  signal(SIGPIPE, SIG_IGN);
  
  ssh_event_loop_initialize();
  
  ssh_agent_open(agent_open_callback, NULL);

  ssh_event_loop_run();
  ssh_event_loop_uninitialize();

  if (dynamic_array)
    {
      for(i = 0; i < num_files ; i++)
        {
          ssh_xfree(files[i]);
        }
      ssh_xfree(files);
    }
  
  ssh_user_free(user, FALSE);
  exit(EXIT_STATUS_OK);
}
