#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

int64_t print(int64_t n) {
  printf("%"PRId64, n);
  return 0;
}

// Does not work until tuple are added to the language
int64_t max(int64_t a, int64_t b) {
  return a > b ? a : b;
}
