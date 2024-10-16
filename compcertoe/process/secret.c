#include <stdio.h>
#include <unistd.h>
char msg[] = "uryyb";

void rot13(char *buf, int n) {}

int main() {
  rot13(msg, sizeof(msg) - 1);
  write(1, msg, sizeof(msg) - 1);
  return 0;
}
