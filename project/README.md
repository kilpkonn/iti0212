Tavo Annus
186060IAIB
taannu


# Building
Make sure to have **idris2** installed.  
Open `StackLang.idr` in REPL.  
```
:c interpret main
```


## Part 4
_I chose to add symbols to complete Turning complete language_  
 
### General remarks
The interpreter starts progressing symbols left to right.
If no action is possible for current elements the interpreter will keep moving 
"cursor" right by poping from right stack and appending to left stack.
If some operation is possible, the operation is performed and cursor will start
moving left again as also new operations may be possible in left stack.
As the symbols on the right are "the future" it is only possible to operate
on elements and operations stored in left stack (past).
  
However, you can jump by n symbols to both directions without progressing
the symbols in between. 
The has to be defined "compile time" but it is possible to dynamically change it
to some extent via if clauses as they allow dropping elements.


### >{n} operator
This operator moves _cursor_ right `n` operations.  
The operation is required to structure more complex programs as otherwise proper
conditionals and loops are impossible.

#### Examples
```bash
echo "1 p 2 p 3 p >5 p 4 p 5 p 6 p 7" > prog && ./interpret prog
# Prints
# Evaluation prints: 1 <- Starts moving right in program and printing
# Evaluation prints: 2
# Evaluation prints: 3
# Evaluation prints: 5 <- Jumped 5 right and stated moving left again
# Evaluation prints: 4 <- Continues printing and moving left
# Evaluation prints: Stack is empty <- All apperations have only access to elements
                                       from it. Since this is leftmost, empty is printed.
# Evaluation prints: 6 <- Moving right again
# 7 <- Only 1 elem left, return it

```


### <{n} operator
This is the opposite of **>{n}** and moves cursor left `n` operations


### <? operator
Compares top 2 elements of stack.
If 2nd element is smaller than top element, 3rd element is thrown away with 1st and 2nd.
Otherwise 3rd element is kept and only top 2 are thrown away.

#### Example
```bash
echo "1 2 3 4 <? p" > prog && ./interpret prog
# Prints
# Evaluation prints: 1 <- 2 is thrown away as 3 < 4
# No Result <- Nothing left
```

### >? operator
Same as **<?** but in the top 2 elements are compared in opposite direction.
If 2nd element is bigger than top element, 3rd element is thrown away with 1st and 2nd.
Otherwise 3rd element is kept and only top 2 elements are thrown away.

#### Example
```bash
echo "1 2 3 4 >? p" > prog && ./interpret prog
# Prints
# Evaluation prints: 2 <- 3rd topmost element is kept
# 1 <- 1 remains in stack under 2.
```

### = Operator
Checks equality of top 2 elements in stack.
If elements are not equal the 3rd topmost element is thrown away.
Otherwise only top 2 elements are thrown away after comaprison.

#### Example
```bash
echo "1 2 3 3 =" > prog && ./interpret prog
# Returns 1 as 2 is thrown away

echo "1 2 3 4 =" > prog && ./interpret prog
# Keeps infinetly looping, as no operations are possible and
# multiple elements exsist in stack.
```

### : operator
Duplicates n elements (specified by second topmost element) 
m times (specified by topmost element)


#### Example
```bash
echo "0 1 2 3 4 >5 p <1 2 3 :" > prog && ./interpret prog
# Prints
# Evaluation prints: 4
# Evaluation prints: 3
# Evaluation prints: 2
# Evaluation prints: 1
# 0
```
Note that `<1` is needed to jump left to p as otherwise it would
start printing previous `p` operators.

#### Some random more complex example
```bash
echo "r 1 b >16 1 d p <3 >3 >3 1 d 2 * 1 b <3 9 >2 r :" > prog && ./interpret prog
```
Will ask input twice and multiply number inserted first with `2` amount of times
entered in second input + 1.  
Loop is used to rising to power.
