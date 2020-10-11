
#include <stdio.h>
#include <stdlib.h>

double getreal() {
  double x;  
  int stt = scanf("%lf", x);
  if (stt != 1) {
      printf("Error getreal()");
      exit(1);
  }
}

void putreal(double n) {
  printf("%lf", n);
}

int main() {
putreal((3) / (0));
return 0;
}
