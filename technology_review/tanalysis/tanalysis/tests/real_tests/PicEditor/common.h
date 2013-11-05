#ifndef __COMMON_H
#define __COMMON_H

#define LOWER_DEATH_LIMIT 25
#define UPPER_DEATH_LIMIT 75
#define LOWER_CHANGE_LIMIT 45
#define UPPER_CHANGE_LIMIT 55

/**
* Reads the configuration file from input_file. Stores in n the size of the cube.
* Returns 0 if success, -1 otherwise.
*/
int read_config(char* input_file, int* n, int* config, int max_size);

/**
* Prints config and alive to the output_file.
* 
*/
int print_config(char* output_file, int n, int g, int* config, int* alive);

/**
* Used for debugging purposes.
*/
int dbg_print_config(int n, int* config);

/**
* Returns 0 if the cell at (x, y, z) will be dead in the next generation,
* 1 otherwise.
*/
int is_alive(int x, int y, int z, int* config, int n);


#endif
