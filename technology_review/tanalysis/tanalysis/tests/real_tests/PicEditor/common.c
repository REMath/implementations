#include <stdio.h>
#include <stdlib.h>
#include "common.h"
#include "utils.h"

int read_config(char* input_file, int* n, int* config, int max_size)
{
	FILE* fi;
	int i, j, k, _n;
	
	fi = fopen(input_file, "r");
	fscanf(fi, "%d", n);
	_n = *n;
	for(i = 0; i < _n; ++ i) {
		for (j = 0; j < _n; ++ j) {
			for (k = 0; k < _n; ++ k) {
				fscanf(fi, "%d", &config[i * _n * _n + j * _n + k]);
			}
		}
	}
		
	fclose(fi);
	return 0;
read_err:
    fclose(fi);	
fopen_err:
	return -1;
}


static inline int max(int x, int y) 
{
	return x < y ? y : x;
}



static inline int min(int x, int y)
{
	return x < y ? x : y;
}


static inline int max_distance(int x, int y, int z)
{
	return (x + y + z) / 5 + 1;
}



int is_alive(int x, int y, int z, int* config, int n)
{
	int i, j, k, d;
	int alive_cnt = 0;
	int cnt = 0;
	int i_min, i_max, j_min, j_max, k_min, k_max;


	d = max_distance(x, y, z);
	i_min = max(x - d, 0);
	i_max = min(x + d + 1, n);
	j_min = max(y - d, 0);
	j_max = min(y + d + 1, n);
	k_min = max(z - d, 0);
	k_max = min(z + d + 1, n);
	for (i = i_min; i < i_max; ++ i) {
		for (j = j_min; j < j_max; ++ j) {
			for (k = k_min; k < k_max; ++ k) {
				if (x == i && y == j && z == k)
					continue;
				if (config[i * n * n + j * n + k]) 
					++ alive_cnt;
				++ cnt;
			}	
		}
	}
	if (alive_cnt * 100 < cnt * LOWER_DEATH_LIMIT)
		return 0;
	
	if (alive_cnt * 100 > cnt * UPPER_DEATH_LIMIT)
		return 0;
	
	if (alive_cnt * 100 > cnt * LOWER_CHANGE_LIMIT && alive_cnt * 100 < cnt * UPPER_CHANGE_LIMIT) {
		if (config[x * n * n + y * n + z]) 
			return 0;
		return 1;
	}
	return 1;
}



int print_config(char* output_file, int n, int g, int* config, int* alive)
{
	FILE* fo;
	int i, j, k;

	CHECK((fo = fopen(output_file, "w")) != NULL, fopen_err, "Unable to open output file");

	for (i = 0; i < n; ++ i) {
		for (j = 0; j < n; ++ j) {
			for (k = 0; k < n; ++ k) {
				CHECK((fprintf(fo, "%d ", config[i * n * n + j * n + k]) != 0), write_err, "Unable to write to output file");
			}
			fprintf(fo, "\n");
		}
		fprintf(fo, "\n");
	}

	for (i = 0; i < g; ++ i) {
		CHECK((fprintf(fo, "%d\n", alive[i]) != 0), write_err, "Unable to write to output file"); 
	}

	fclose(fo);
	return 0;
write_err:
	fclose(fo);
fopen_err:
	return -1;
}

int dbg_print_config(int n, int* config)
{
	int i, j, k;

	for (i = 0; i < n; ++ i) {
		for (j = 0; j < n; ++ j) {
			for (k = 0; k < n; ++ k) {
				printf("%d ", config[i * n * n + j * n + k]);
			}
			printf("\n");
		}
		printf("\n\n");
	}
	printf("\n");

	return 0;
}


