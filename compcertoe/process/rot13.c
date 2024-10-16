#include <unistd.h>

char rot13(char c) {
  if (c >= 'a' && c <= 'z') {
    return 'a' + (c - 'a' + 13) % 26;
  } else {
    return c;
  }
}

int main() {
  char buf[100];
  int n = read(0, buf, sizeof(buf));
  for (int i = 0; i < n; i++) {
    buf[i] = rot13(buf[i]);
  }
  write(1, buf, n);
  return 0;
}
