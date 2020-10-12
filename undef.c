
#include <stdio.h>
#include <stdlib.h>

double getreal() {
  double x;  
  int stt = scanf("%lf", &x);
  if (stt == -1) {
    printf("Unexpected EOF");
    exit(1);
  } else if (stt != 1) {
      printf("Error getreal()");
      exit(1);
  }
  return x;
}

void putreal(double n) {
  printf("%lf\n", n);
}

int main() {
putreal(foo);
return 0;
}
