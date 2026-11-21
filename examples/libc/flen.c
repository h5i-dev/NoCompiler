/* The length of the file named by argv[1], in decimal, on stdout: musl's
   startup, fopen/fread/fclose, fwrite to stdout, exit. */
#include <stdio.h>

int main(int argc, char **argv) {
  if (argc < 2) return 2;
  FILE *f = fopen(argv[1], "rb");
  if (!f) return 1;
  unsigned long n = 0;
  char buf[64];
  size_t k;
  while ((k = fread(buf, 1, sizeof buf, f)) > 0) n += k;
  fclose(f);
  char out[24];
  int i = 23;
  out[i] = '\n';
  do { out[--i] = '0' + n % 10; n /= 10; } while (n);
  fwrite(out + i, 1, 24 - i, stdout);
  return 0;
}
