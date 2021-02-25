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
        .block_group = 0,
        .nlink = 1,
        .uid = 0,
        .gid = 0,
        .mode = 16877,
        .rdev = 0,
        .flags = 0,
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
        .ctime = struct btrfs_timespec {
            .sec = 0,
            .nsec = 0,
        },
        .mtime = struct btrfs_timespec {
            .sec = 0,
            .nsec = 0,
        },
        .otime = struct btrfs_timespec {
            .sec = 0,
            .nsec = 0,
        },
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
$ sudo ./target/debug/btrd
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

### Built-in functions

#### `key(min_objectid, min_type, min_offset, min_transid)`

Returns a `struct _btrfs_ioctl_search_key` with the minimums sets to the
corresponding arguments.

If you want to set maximum values, simply modify the returned struct.

#### `keyof(expr)`

Returns the corresponding disk key of the expression.

Will raise an error if `expr` does not resolve to a top-level on-disk struct
(top level meaning not nested).

#### `search(tree_id, key)`

Returns an array of search results based on `tree_id` and `key`, where `key`
must be type `struct _btrfs_ioctl_search_key`.

#### `typeof(expr)`

Returns the type of the expression in string form.

#### `len(expr)`

Returns the length of the array.

Will raise an error if `expr` does not resolve to an array.

[0]: https://en.wikipedia.org/wiki/Read%E2%80%93eval%E2%80%93print_loop
