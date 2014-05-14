#include <stdio.h>
#include <stdlib.h>
#include "common.h"
#include "utils.h"


#define MAX_N 128
#define MAX_CELLS (MAX_N * MAX_N * MAX_N)
#define MAX_G 256

int cube[MAX_CELLS], alive[MAX_G], tmp_cube[MAX_CELLS];
int n, g;

int main(int argc, char** argv) 
{
	int i, j, k, cnt;
	int* old_config;
	int* curr_config;
	int* aux;

	g = strtol(argv[1], (char **)NULL, 10);

	CHECK((read_config(argv[2], &n, cube, MAX_N) == 0), err, "Unable to read initial config");

	old_config = cube;
	curr_config = tmp_cube;
	for (cnt = 0; cnt < g; ++ cnt) {
		for (i = 0; i < n; ++ i) {
			for (j = 0; j < n; ++ j) {
				for (k = 0; k < n; ++ k) {
					if (is_alive(i, j, k, old_config, n)) {
						curr_config[i * n * n + j * n + k] = 1;
						++ alive[cnt];
					} else {
						curr_config[i * n * n + j * n + k] = 0;
					}
				}
			}
		}
		aux = old_config;
		old_config = curr_config;
		curr_config = aux;
	}

	exit(print_config(argv[3], n , g, old_config, alive));

err:
	exit(1);
}
