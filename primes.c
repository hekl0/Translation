
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
double n;
n = getreal();
double cp;
cp = 2;
while (n > 0) {
double found;
found = 0;
double cf1;
cf1 = 2;
double cf1s;
cf1s = (cf1) * (cf1);
while (cf1s <= cp) {
double cf2;
cf2 = 2;
double pr;
pr = (cf1) * (cf2);
while (pr <= cp) {
if (pr == cp) {
found = 1;
}
cf2 = (cf2) + (1);
pr = (cf1) * (cf2);
}
cf1 = (cf1) + (1);
cf1s = (cf1) * (cf1);
}
if (found == 0) {
putreal(cp);
n = (n) - (1);
}
cp = (cp) + (1);
}
return 0;
}
