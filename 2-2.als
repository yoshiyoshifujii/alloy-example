module tour/addressBook1

sig Name, Addr { }
sig Book {
	addr: Name -> lone Addr
}

pred add (b, b': Book, n: Name, a: Addr) {
	b'.addr = b.addr + n -> a
}
run add for 3 but 2 Book
