all: architecture.png

%.png: %.dot
	dot $< -o $@ -T png

clean:
	rm -f *.png

.PHONY: all clean
