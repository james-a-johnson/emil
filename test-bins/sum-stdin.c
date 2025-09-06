#include <stdio.h>

int main() {
  unsigned int sum = 0;
  unsigned int val = 0;
  while (1) {
    int bytes = fscanf(stdin, "%u\n", &val);
    if (bytes <= 0) { break; }
    sum += val;
  }
  printf("%d\n", sum);
  return 0;
}
