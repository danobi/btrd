# btrd
The btrfs debugger (pronounced "buttered").

`btrd` is a [REPL][0] debugger that helps inspect mounted btrfs filesystems.
btrd is particularly useful in exploring on-disk structures and has full
knowledge of all on-disk types.

### Demo

```
$ sudo btrd
btrd (the btrfs debugger) v0.1.0
Type 'help' for help

(btrd) filesystem "/mnt/btrfs"
(btrd) k = key(BTRFS_DEV_TREE_OBJECTID, BTRFS_ROOT_ITEM_KEY, 0, 0)
(btrd) print k
struct _btrfs_ioctl_search_key {
    .min_objectid = 4,
    .max_objectid = 18446744073709551615,
    .min_type = 132,
    .max_type = 255,
    .min_offset = 0,
    .max_offset = 18446744073709551615,
    .min_transid = 0,
    .max_transid = 18446744073709551615,
}

(btrd) res = search(BTRFS_ROOT_TREE_OBJECTID, k)
(btrd) len(res)
297

(btrd) res[0]
struct btrfs_root_item {
    .inode = struct btrfs_inode_item {
        .generation = 1,
        .transid = 0,
        .size = 3,
        .nbytes = 16384,
<...>
        .sequence = 0,
        .reserved = [
            0,
            0,
            0,
            0,
        ],
        .atime = struct btrfs_timespec {
            .sec = 0,
            .nsec = 0,
        },
<...>

(btrd) print res[0].inode.nbytes
16384

(btrd) typeof(res[0])
"struct btrfs_root_item"

(btrd) keyof(res[0])
struct btrfs_key {
    .objectid = 4,
    .type = 132,
    .offset = 0,
}
```

### Building

```bash
$ git clone https://github.com/danobi/btrd.git
$ cd btrd
$ cargo build --release
$ sudo ./target/release/btrd
```

### Language features

btrd's scripting language is not a hack -- it's a dynamically typed language
tailored to filesystem debugging. The following is a list of language features:

Types:

* Strings
* Integers (all integers are internally represented as i128)
* Booleans
* Arrays (may not be user instantiated)
* Structs (may not be user defined/instantiated)
* Functions (first-class support; may not be user defined)

Expressions:

* Binary expressions (`+`, `-`, `/`, `%`, `>>`, `&&`, `==`, etc.)
* Unary expressions (`-`, `~`, `!`)
* Parentheses
* Function calls
* Struct field access
* Array indexes

Control flow:

* `while`
* `for` (ranged based)
* `if/else`

There is not and **will not** be support for:

* Floating point

[0]: https://en.wikipedia.org/wiki/Read%E2%80%93eval%E2%80%93print_loop
