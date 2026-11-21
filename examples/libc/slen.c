/* The length of standard input, in decimal, on stdout: musl's startup,
   fread on stdin, fwrite to stdout, exit. No allocation. */
#include <stdio.h>

int main(void) {
  unsigned long n = 0;
  char buf[64];
  size_t k;
  while ((k = fread(buf, 1, sizeof buf, stdin)) > 0) n += k;
  char out[24];
  int i = 23;
  out[i] = '\n';
  do { out[--i] = '0' + n % 10; n /= 10; } while (n);
  fwrite(out + i, 1, 24 - i, stdout);
  return 0;
}
