#ifndef __UTILS_H
#define __UTILS_H

#include <stdio.h>

#define CHECK(condition, error_label, error_message) \
	do { \
		if (!(condition)) { \
			perror(error_message); \
			goto error_label; \
		} \
	} while(0)

#endif
