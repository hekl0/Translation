
#include <stdio.h>
#include <stdlib.h>

double getreal() {
  ... // returns a real number from standard input or
      // prints an appropriate error message and dies.
}

void putreal(double n) {
  ... // prints a real number and a linefeed to standard output.
}
int main() {
    n = getreal();
    cp = 2;
    while (n > 0) {
    found = 0;
    cf1 = 2;
    cf1s = (cf1) * (cf1);
    while (cf1s <= cp) {
    cf2 = 2;
    pr = (cf1) * ((cf2) + (cf1));
    while (pr <= cp) {
    if (pr = cp) {
    found = 1;
    }
    cf2 = (cf2) + (1);
    pr = (cf1) * (cf2);
    }
    cf1 = (cf1) + (1);
    cf1s = (cf1) * (cf1);
    }
    if (found = 0) {
    putreal(cp);
    n = (n) - (1);
    }
    cp = (cp) + (1);
    }
}
