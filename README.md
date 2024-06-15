# Lambda C

Small interpreter for lambda calculus.

## Syntax

While a print statement allows you to print an expression

```
# Statements
let [name] = [expr] # Defines a value
print [expr]        # Prints an expression

# Expression
$[arg_name]. [expr]     # A lambda expression (an anonymous function)
[func] [arg]            # Evaluates a lambda by substituting its argument with [arg]
[name]                  # Resolves to a global or an argument
(...)                   # Parenthesis to resolve order

[func] [a1] [a2]        # Resolves like `([func] [a1]) [a2]`
[func] $x. [expr]       # Resolves like `[func] ($x. [expr])`
$x. [func] [a1] [a2]    # Resolves like `$x. (([func] [a1]) [a2])`
```
