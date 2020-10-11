
#include <stdio.h>
#include <stdlib.h>

double getreal() {
  double x;  
  int stt = scanf("%lf", x);
  printf("%d", stt);
  if (stt == -1) {
      printf("Unexpected EOF");
      exit(1);
  } else {
      printf("Wrong input type");
      exit(1);
  }
}

void putreal(double n) {
  printf("%lf", n);
}

int main() {
double n = getreal();
return 0;
}
