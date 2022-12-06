CC       = g++
CFLAGS   = -Wall -g
LDFLAGS  = -lreadline
OBJFILES = main.o
TARGET   = main

all: $(TARGET)

$(TARGET): $(OBJFILES)
	$(CC) $(CFLAGS) -o $(TARGET) $(OBJFILES) $(LDFLAGS)

clean:
	rm -f $(OBJFILES) $(TARGET) *~