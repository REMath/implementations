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
	int i, cnt;
	int* old_config;
	int* curr_config;
	int* aux;
	int n_n_n;
	int n_n;

	g = strtol(argv[1], (char **)NULL, 10);

	CHECK((read_config(argv[2], &n, cube, MAX_N) == 0), err, "Unable to read initial config");

	n_n_n = n * n * n;
	n_n = n * n;

	old_config = cube;
	curr_config = tmp_cube;
	
	for (cnt = 0; cnt < g; ++ cnt) {
		int tmp_alive = 0;

		//#pragma omp parallel for private(i) schedule(runtime) reduction(+:tmp_alive)
		for (i = 0; i < n_n_n; ++ i) {
			int x, y, z;

			x = i / n_n;
			y = (i % n_n) / n;
			z = (i % n_n) % n;
			if (is_alive(x, y, z, old_config, n)) {
				curr_config[i] = 1;
				++ tmp_alive;
			} else {
				curr_config[i] = 0;
			}
		}
		alive[cnt] = tmp_alive;
		aux = old_config;
		old_config = curr_config;
		curr_config = aux;
	}

	exit(print_config(argv[3], n , g, old_config, alive));

err:
	exit(1);
}

