#include "strTheory.h"


std::string inputFile;

/**
 * Test Procedural Attachment Theory.
 */
void pa_theory_example()
{
  if(inputFile == "")
  {
    printf("No input file is provided.\n");
    return;
  }
  Z3_context ctx = mk_my_context();
  Z3_theory Th = mk_pa_theory(ctx);
  ctx = Z3_theory_get_context(Th);

  // load cstr from inputFile
  Z3_ast fs = Z3_parse_smtlib2_file(ctx, inputFile.c_str(), 0, 0, 0, 0, 0, 0);

#ifdef DEBUGLOG
  __debugPrint(logFile, "\nInput loaded:\n-----------------------------------------------\n");
  printZ3Node(Th, fs);
  __debugPrint(logFile, "\n-----------------------------------------------\n");
#endif

  Z3_assert_cnstr(ctx, fs);
  check(ctx);
  Z3_del_context(ctx);
}


int main(int argc, char ** argv)
{
  logFile = NULL;
  std::string primStr;
  inputFile = std::string("");
  int c;

  static struct option long_options[] =
  {
    {"nolog",     no_argument, 0, 'n'},
    {"showCtx",   required_argument, 0, 's'},
    {0, 0, 0, 0}
  };

  while (1)
  {
    int option_index = 0;
    c = getopt_long (argc, argv, "nsp:c:b:f:", long_options, &option_index);

    if (c == -1)
      break;

    switch (c)
    {
      case 'n': {
        logFile = fopen("/dev/null", "w");
        break;
      }
      case 'f': {
        inputFile = std::string(optarg);
        break;
      }
      default:
        exit(0);
    }
  }

#ifdef DEBUGLOG
  if(logFile == NULL)
    logFile = fopen("log", "w");
  __debugPrint(logFile, "Input file: %s\n", inputFile.c_str() );
#endif

  pa_theory_example();

#ifdef DEBUGLOG
  fclose(logFile);
#endif

  return 0;
}


