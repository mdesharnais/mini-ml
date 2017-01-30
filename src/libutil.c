#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

int64_t print(int64_t n) {
  printf("%"PRId64"\n", n);
  return 0;
}

int64_t printheader(int64_t n) {
  printf("P3\n400\n400\n60\n");
  return 0;
}

int64_t printdot(int64_t n) {
  int64_t h = 6*n*1024/60;
  int64_t i = 6*n/60;
  int64_t t = h - i*1024;
  int64_t q = 1024 - t;

  if (59 < n) {
    print(0);
    print(0);
    print(0);
  } else if (i < 1) {
    print(60);
    print(60*t/1024);
    print(0);
  } else if (i < 2) {
    print(60*q/1024);
    print(60);
    print(0);
  } else if (i < 3) {
    print(0);
    print(60);
    print(60*t/1024);
  } else if (i < 4) {
    print(60);
    print(60*q/1024);
    print(60);
  } else if (i < 5) {
    print(60*t/1024);
    print(0);
    print(60);
  } else {
    print(60);
    print(0);
    print(60*q/1024);
  }
  return 0;
}

int64_t impl1(int64_t n) {
  return (n * n) / 1024;
}

int64_t impl2(int64_t n) {
  return 2 * n * n / 1024;
}

// Does not work until tuple are added to the language
int64_t max(int64_t a, int64_t b) {
  return a > b ? a : b;
}
