logd: stringBuffers.o sockets.o threading.o logd.o
	gcc -o logd $^

verify: logd.c
	verifast $(VFFLAGS) stringBuffers.o sockets.o threading.o logd.c
