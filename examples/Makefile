.PHONY: default
default:
	make -C limited-order-book clean
	make -C limited-order-book
	make -C chacha20 clean
	make -C chacha20
	OTHERFLAGS="--lax" make -C sha256 clean
	OTHERFLAGS="--lax" make -C sha256
