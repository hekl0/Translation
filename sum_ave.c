
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
a = getreal();
b = getreal();
sum = (a) + (b);
putreal(sum);
putreal((sum) / (2));
return 0;
}
