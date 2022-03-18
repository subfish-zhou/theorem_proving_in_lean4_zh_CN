归纳和递归
=======================

在上一章中，我们看到归纳定义提供了在Lean中引入新类型的强大手段。此外，构造子和递归子提供了在这些类型上定义函数的唯一手段。命题即类型的对应关系，意味着归纳法是证明的基本方法。

Lean提供了定义递归函数、执行模式匹配和编写归纳证明的自然方法。它允许你通过指定它应该满足的方程来定义一个函数，它允许你通过指定如何处理可能出现的各种情况来证明一个定理。在它内部，这些描述被“方程编译器”程序“编译”成原始递归子。方程编译器不是可信代码库的一部分；它的输出包括由内核独立检查的项。

模式匹配
----------------

对示意图模式的解释是编译过程的第一步。我们已经看到，`casesOn`递归子可以通过分情况讨论来定义函数和证明定理，根据归纳定义类型所涉及的构造子。但是复杂的定义可能会使用几个嵌套的``casesOn``应用，而且可能很难阅读和理解。模式匹配提供了一种更方便的方法，并且为函数式编程语言的用户所熟悉。

考虑一下自然数的归纳定义类型。每个自然数要么是``zero``，要么是``succ x``，因此你可以通过在每个情况下指定一个值来定义一个从自然数到任意类型的函数:

```lean
open Nat

def sub1 : Nat → Nat
  | zero   => zero
  | succ x => x

def isZero : Nat → Bool
  | zero   => true
  | succ x => false
```

用来定义这些函数的方程在定义上是成立的：

```lean
example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := rfl

example : sub1 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl
```

我们可以用一些更耳熟能详的符号，而不是``zero``和``succ``：

```lean
def sub1 : Nat → Nat
  | 0   => 0
  | x+1 => x

def isZero : Nat → Bool
  | 0   => true
  | x+1 => false
```

因为加法和零符号已经被赋予`[matchPattern]`属性，它们可以被用于模式匹配。Lean简单地将这些表达式规范化，直到显示构造子``zero``和``succ``。

模式匹配适用于任何归纳类型，如乘积和选项类型：

```lean
def swap : α × β → β × α
  | (a, b) => (b, a)

def foo : Nat × Nat → Nat
  | (m, n) => m + n

def bar : Option Nat → Nat
  | some n => n + 1
  | none   => 0
```

在这里，我们不仅用它来定义一个函数，而且还用它来进行案例证明：

```lean
# namespace Hidden
def not : Bool → Bool
  | true  => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true  => rfl  -- proof that not (not true) = true
  | false => rfl  -- proof that not (not false) = false
# end Hidden
```

模式匹配也可以用来解构归纳定义的命题：

```lean
example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq
```

这样解决带逻辑连接词的命题就很紧凑。

在所有这些例子中，模式匹配被用来进行单一案例的区分。更有趣的是，模式可以涉及嵌套的构造子，如下面的例子。

```lean
def sub2 : Nat → Nat
  | 0   => 0
  | 1   => 0
  | x+2 => x
```

方程编译器首先对输入是``zero``还是``succ x``的形式进行分类讨论。 然后对`x`是``zero``还是``succ x``的形式进行分类讨论。它从提交给它的模式中确定必要的案例拆分，如果模式不能穷尽案例，则会引发错误。同时，我们可以使用算术符号，如下面的版本。在任何一种情况下，定义方程都是成立的。

```lean
# def sub2 : Nat → Nat
#   | 0   => 0
#   | 1   => 0
#   | x+2 => x
example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x+2) = x := rfl

example : sub2 5 = 3 := rfl
```

你可以写``#print sub2``来看看这个函数是如何被编译成递归子的。(Lean会告诉你`sub2`已经被定义为内部辅助函数`sub2.match_1`，但你也可以把它打印出来)。Lean使用这些辅助函数来编译`match`表达式。实际上，上面的定义被扩展为

```lean
def sub2 : Nat → Nat :=
  fun x =>
    match x with
    | 0   => 0
    | 1   => 0
    | x+2 => x
```

下面是一些嵌套模式匹配的例子：

```lean
example (p q : α → Prop)
        : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

def foo : Nat × Nat → Nat
  | (0, n)     => 0
  | (m+1, 0)   => 1
  | (m+1, n+1) => 2
```

方程编译器可以按顺序处理多个参数。例如，将前面的例子定义为两个参数的函数会更自然：

```lean
def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2
```

另一例：

```lean
def bar : List Nat → List Nat → Nat
  | [],      []      => 0
  | a :: as, []      => a
  | [],      b :: bs => b
  | a :: as, b :: bs => a + b
```

这些模式是由逗号分隔的。

在下面的每个例子中，尽管其他参数包括在模式列表中，但只对第一个参数进行了分割。

```lean
# namespace Hidden
def and : Bool → Bool → Bool
  | true,  a => a
  | false, _ => false

def or : Bool → Bool → Bool
  | true,  _ => true
  | false, a => a

def cond : Bool → α → α → α
  | true,  x, y => x
  | false, x, y => y
# end Hidden
```

还要注意的是，当定义中不需要一个参数的值时，你可以用下划线来代替。这个下划线被称为*通配符模式*，或*匿名变量*。与方程编译器之外的用法不同，这里的下划线并*不*表示一个隐参数。使用下划线表示通配符在函数式编程语言中是很常见的，所以Lean采用了这种符号。[通配符和重叠模式](#通配符和重叠模式)一节阐述了通配符的概念，而[不可访问模式](#inaccessible_terms)一节解释了你如何在模式中使用隐参数。

正如[归纳类型](./inductive_types.md)一章中所描述的，归纳数据类型可以依赖于参数。下面的例子使用模式匹配定义了``tail``函数。参数``α : Type``是一个参数，出现在冒号之前，表示它不参与模式匹配。Lean也允许参数出现在``:``之后，但它不能对其进行模式匹配。

```lean
def tail1 {α : Type u} : List α → List α
  | []      => []
  | a :: as => as

def tail2 : {α : Type u} → List α → List α
  | α, []      => []
  | α, a :: as => as
```

尽管参数``α``在这两个例子中的位置不同，但在这两种情况下，它的处理方式是一样的，即它不参与案例分割。

Lean也可以处理更复杂的模式匹配形式，其中从属类型的参数对各种情况构成了额外的约束。这种*依赖模式匹配*的例子在[依赖模式匹配](#dependent_pattern_matching)一节中考虑。

通配符和重叠模式
----------------------------------

考虑上节的一个例子：

```lean
def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2
```

```lean
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
```

在第二种表述中，模式是重叠的；例如，一对参数``0 0``符合所有三种情况。但是Lean通过使用第一个适用的方程来处理这种模糊性，所以在这个例子中，最终结果是一样的。特别是，以下方程在定义上是成立的：

```lean
# def foo : Nat → Nat → Nat
#   | 0, n => 0
#   | m, 0 => 1
#   | m, n => 2
example : foo 0     0     = 0 := rfl
example : foo 0     (n+1) = 0 := rfl
example : foo (m+1) 0     = 1 := rfl
example : foo (m+1) (n+1) = 2 := rfl
```

由于不需要``m``和``n``的值，我们也可以用通配符模式代替。

```lean
def foo : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2
```

你可以检查这个``foo``的定义是否满足与之前相同的定义特性。

一些函数式编程语言支持*不完整的模式*。在这些语言中，解释器对不完整的情况产生一个异常或返回一个任意的值。我们可以使用``Inhabited``（含元素的）类型类来模拟任意值的方法。粗略的说，``Inhabited α``的一个元素是对``α``拥有一个元素的见证；在[类型类](./type_classes.md)中，我们将看到Lean可以被告知合适的基础类型是含元素的，并且可以自动推断出其他构造类型是含元素的。在此基础上，标准库提供了一个任意元素``arbitrary``，任何含元素的类型。

我们还可以使用类型`Option α`来模拟不完整的模式。我们的想法是对所提供的模式返回`some a`，而对不完整的情况使用`none`。下面的例子演示了这两种方法。

```lean
def f1 : Nat → Nat → Nat
  | 0, _  => 1
  | _, 0  => 2
  | _, _  => arbitrary  -- the "incomplete" case

example : f1 0     0     = 1 := rfl
example : f1 0     (a+1) = 1 := rfl
example : f1 (a+1) 0     = 2 := rfl
example : f1 (a+1) (b+1) = arbitrary := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _  => some 1
  | _, 0  => some 2
  | _, _  => none     -- the "incomplete" case

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl
```

The equation compiler is clever. If you leave out any of the cases in the following definition, the error message will let you know what has not been covered.

方程编译器是很聪明的。如果你遗漏了以下定义中的任何一种情况，错误信息会告诉你遗漏了哪个。

```lean
def bar : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0
  | 0,   b :: _, _     => b
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b
```

某些情况也可以用“if ... then ... else”代替``casesOn``。

```lean
def foo : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3

#print foo.match_1
```

结构化递归和归纳
----------------------------------

方程编译器的强大之处在于，它还支持递归定义。在接下来的三节中，我们将分别介绍。

- 结构性递归定义
- 有根有据的递归定义
- 相互递归的定义

一般来说，方程编译器处理以下形式的输入。

What makes the equation compiler powerful is that it also supports recursive definitions. In the next three sections, we will describe, respectively:

- structurally recursive definitions
- well-founded recursive definitions
- mutually recursive definitions

Generally speaking, the equation compiler processes input of the following form:

```
def foo (a : α) : (b : β) → γ
  | [patterns₁] => t₁
  ...
  | [patternsₙ] => tₙ
```

这里`(a : α)`是一个参数序列，`(b : β)`是进行模式匹配的参数序列，`γ`是任何类型，它可以取决于`a`和`b``。每一行应该包含相同数量的模式，`β``的每个元素都有一个。正如我们所看到的，模式要么是一个变量，要么是应用于其他模式的构造函数，要么是一个归一化为该形式的表达式（其中非构造函数用``[matchPattern]``属性标记）。构造函数的出现会提示案例拆分，构造函数的参数由给定的变量表示。在[依赖模式匹配](#dependent_pattern_matching)一节中，我们将看到有时有必要在模式中包含明确的术语，这些术语需要进行表达式类型检查，尽管它们在模式匹配中没有起到作用。由于这个原因，这些被称为 "不可访问的模式"。但是在[依赖模式匹配](#dependent_pattern_matching)一节之前，我们将不需要使用这种不可访问的模式。

正如我们在上一节所看到的，术语`t₁，...，tₙ`可以利用任何一个参数`a`，以及在相应模式中引入的任何一个变量。使得递归和归纳成为可能的是，它们也可以涉及对``foo``的递归调用。在本节中，我们将处理*结构性递归*，其中`foo'的参数出现在`:='的右侧，是左侧模式的子项。我们的想法是，它们在结构上更小，因此在归纳类型中出现在更早的阶段。下面是上一章的一些结构递归的例子，现在用方程编译器来定义。

Here ``(a : α)`` is a sequence of parameters, ``(b : β)`` is the sequence of arguments on which pattern matching takes place, and ``γ`` is any type, which can depend on ``a`` and ``b``. Each line should contain the same number of patterns, one for each element of ``β``. As we have seen, a pattern is either a variable, a constructor applied to other patterns, or an expression that normalizes to something of that form (where the non-constructors are marked with the ``[matchPattern]`` attribute). The appearances of constructors prompt case splits, with the arguments to the constructors represented by the given variables. In [Section Dependent Pattern Matching](#dependent_pattern_matching), we will see that it is sometimes necessary to include explicit terms in patterns that are needed to make an expression type check, though they do not play a role in pattern matching. These are called "inaccessible patterns" for that reason. But we will not need to use such inaccessible patterns before [Section Dependent Pattern Matching](#dependent_pattern_matching).

As we saw in the last section, the terms ``t₁, ..., tₙ`` can make use of any of the parameters ``a``, as well as any of the variables that are introduced in the corresponding patterns. What makes recursion and induction possible is that they can also involve recursive calls to ``foo``. In this section, we will deal with *structural recursion*, in which the arguments to ``foo`` occurring on the right-hand side of the ``:=`` are subterms of the patterns on the left-hand side. The idea is that they are structurally smaller, and hence appear in the inductive type at an earlier stage. Here are some examples of structural recursion from the last chapter, now defined using the equation compiler:

```lean
open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat)   : add m zero = m := rfl
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add : ∀ n, add zero n = n
  | zero   => rfl
  | succ n => congrArg succ (zero_add n)

def mul : Nat → Nat → Nat
  | n, zero   => zero
  | n, succ m => add (mul n m) n
```

The proof of ``zero_add`` makes it clear that proof by induction is really a form of recursion in Lean.

The example above shows that the defining equations for ``add`` hold definitionally, and the same is true of ``mul``. The equation compiler tries to ensure that this holds whenever possible, as is the case with straightforward structural induction. In other situations, however, reductions hold only *propositionally*, which is to say, they are equational theorems that must be applied explicitly. The equation compiler generates such theorems internally. They are not meant to be used directly by the user; rather, the `simp` tactic is configured to use them when necessary. Thus both of the following proofs of `zero_add` work:

```lean
open Nat
# def add : Nat → Nat → Nat
#   | m, zero   => m
#   | m, succ n => succ (add m n)
theorem zero_add : ∀ n, add zero n = n
  | zero   => by simp [add]
  | succ n => by simp [add, zero_add]
```

<!--
In fact, because in this case the defining equations hold
definitionally, we can use `dsimp`, the simplifier that uses
definitional reductions only, to carry out the first step.

.. code-block:: lean

    namespace hidden

    inductive nat : Type
    | zero : nat
    | succ : nat → nat

    namespace nat

    def add : nat → nat → nat
    | m zero     := m
    | m (succ n) := succ (add m n)

    local infix ` + ` := add

    -- BEGIN
    theorem zero_add : ∀ n, zero + n = n
    | zero     := by dsimp [add]; reflexivity
    | (succ n) := by dsimp [add]; rw [zero_add n]
    -- END

    end nat
    end hidden
-->

As with definition by pattern matching, parameters to a structural recursion or induction may appear before the colon. Such parameters are simply added to the local context before the definition is processed. For example, the definition of addition may also be written as follows:

```lean
open Nat
def add (m : Nat) : Nat → Nat
  | zero   => m
  | succ n => succ (add m n)
```

You can also write the example above using `match`.

```lean
open Nat
def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)
```

A more interesting example of structural recursion is given by the Fibonacci function ``fib``.

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n + 2) = fib (n + 1) + fib n := rfl

example : fib 7 = 21 := rfl
```

Here, the value of the ``fib`` function at ``n + 2`` (which is definitionally equal to ``succ (succ n)``) is defined in terms of the values at ``n + 1`` (which is definitionally equivalent to ``succ n``) and the value at ``n``. This is a notoriously inefficient way of computing the fibonacci function, however, with an execution time that is exponential in ``n``. Here is a better way:

```lean
def fibFast (n : Nat) : Nat :=
  (loop n).1
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100
```

Here is the same definition using a `let rec` instead of a `where`.

```lean
def fibFast (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).1
```

In both cases, Lean generates the auxiliary function `fibFast.loop`.

To handle structural recursion, the equation compiler uses *course-of-values* recursion, using constants ``below`` and ``brecOn`` that are automatically generated with each inductively defined type. You can get a sense of how it works by looking at the types of ``Nat.below`` and ``Nat.brecOn``:

```lean
variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)

#reduce @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)
```

The type ``@Nat.below C (3 : nat)`` is a data structure that stores elements of ``C 0``, ``C 1``, and ``C 2``. The course-of-values recursion is implemented by ``Nat.brecOn``. It enables us to define the value of a dependent function of type ``(n : Nat) → C n`` at a particular input ``n`` in terms of all the previous values of the function, presented as an element of ``@Nat.below C n``.

The use of course-of-values recursion is one of the techniques the equation compiler uses to justify to the Lean kernel that a function terminates. It does not affect the code generator which compiles recursive functions as other functional programming language compilers. Recall that `#eval fib <n>` is exponential on `<n>`. On the other hand, `#reduce fib <n>` is efficient because it uses the definition sent to the kernel that is based on the `brecOn` construction.

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

-- #eval fib 50 -- slow
#reduce fib 50  -- fast

#print fib
```

Another good example of a recursive definition is the list ``append`` function.

```lean
def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl
```

Here is another: it adds elements of the first list to elements of the second list, until one of the two lists runs out.

```lean
def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10]
-- [5, 7, 9]
```

You are encouraged to experiment with similar examples in the exercises below.

<a name="_well_founded_recursion_and_induction:"></a> Well-Founded Recursion and Induction
------------------------------------

依赖类型论强大到足以编码和论证有根有据的递归。让我们从理解它的工作原理所需的逻辑背景开始。

Lean的标准库定义了两个谓词，``Acc r a``和``WellFounded r``，其中``r``是一个类型``α``上的二元关系，``a``是一个类型``α``的元素。

Dependent type theory is powerful enough to encode and justify well-founded recursion. Let us start with the logical background that is needed to understand how it works.

Lean's standard library defines two predicates, ``Acc r a`` and ``WellFounded r``, where ``r`` is a binary relation on a type ``α``, and ``a`` is an element of type ``α``.

```lean
variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)
```

The first, ``Acc``, is an inductively defined predicate. According to its definition, ``Acc r x`` is equivalent to ``∀ y, r y x → Acc r y``. If you think of ``r y x`` as denoting a kind of order relation ``y ≺ x``, then ``Acc r x`` says that ``x`` is accessible from below, in the sense that all its predecessors are accessible. In particular, if ``x`` has no predecessors, it is accessible. Given any type ``α``, we should be able to assign a value to each accessible element of ``α``, recursively, by assigning values to all its predecessors first.

The statement that ``r`` is well founded, denoted ``WellFounded r``, is exactly the statement that every element of the type is accessible. By the above considerations, if ``r`` is a well-founded relation on a type ``α``, we should have a principle of well-founded recursion on ``α``, with respect to the relation ``r``. And, indeed, we do: the standard library defines ``WellFounded.fix``, which serves exactly that purpose.

```lean
set_option codegen false
def f {α : Sort u}
      (r : α → α → Prop)
      (h : WellFounded r)
      (C : α → Sort v)
      (F : (x : α) → ((y : α) → r y x → C y) → C x)
      : (x : α) → C x := WellFounded.fix h F
```

There is a long cast of characters here, but the first block we have already seen: the type, ``α``, the relation, ``r``, and the assumption, ``h``, that ``r`` is well founded. The variable ``C`` represents the motive of the recursive definition: for each element ``x : α``, we would like to construct an element of ``C x``. The function ``F`` provides the inductive recipe for doing that: it tells us how to construct an element ``C x``, given elements of ``C y`` for each predecessor ``y`` of ``x``.

Note that ``WellFounded.fix`` works equally well as an induction principle. It says that if ``≺`` is well founded and you want to prove ``∀ x, C x``, it suffices to show that for an arbitrary ``x``, if we have ``∀ y ≺ x, C y``, then we have ``C x``.

In the example above we set the option `codegen` to false because the code generator currently does not support `WellFounded.fix`. The function `WellFounded.fix` is another tool Lean uses to justify that a function terminates.

Lean knows that the usual order ``<`` on the natural numbers is well founded. It also knows a number of ways of constructing new well founded orders from others, for example, using lexicographic order.

Here is essentially the definition of division on the natural numbers that is found in the standard library.

```lean
open Nat

theorem div_rec_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (div_rec_lemma h) y + 1
  else
    zero

set_option codegen false
def div := WellFounded.fix (measure id).wf div.F

#reduce div 8 2 -- 4
```

The definition is somewhat inscrutable. Here the recursion is on ``x``, and ``div.F x f : Nat → Nat`` returns the "divide by ``y``" function for that fixed ``x``. You have to remember that the second argument to ``div.F``, the recipe for the recursion, is a function that is supposed to return the divide by ``y`` function for all values ``x₁`` smaller than ``x``.

The equation compiler is designed to make definitions like this more convenient. It accepts the following:

**TODO: waiting for well-founded support in Lean 4**

.. code-block:: lean

    namespace hidden
    open nat

    -- BEGIN
    def div : ℕ → ℕ → ℕ
    | x y :=
      if h : 0 < y ∧ y ≤ x then
        have x - y < x,
          from sub_lt (lt_of_lt_of_le h.left h.right) h.left,
        div (x - y) y + 1
      else
        0
    -- END

    end hidden

When the equation compiler encounters a recursive definition, it first
tries structural recursion, and only when that fails, does it fall
back on well-founded recursion. In this case, detecting the
possibility of well-founded recursion on the natural numbers, it uses
the usual lexicographic ordering on the pair ``(x, y)``. The equation
compiler in and of itself is not clever enough to derive that ``x -
y`` is less than ``x`` under the given hypotheses, but we can help it
out by putting this fact in the local context. The equation compiler
looks in the local context for such information, and, when it finds
it, puts it to good use.

The defining equation for ``div`` does *not* hold definitionally, but
the equation is available to ``rewrite`` and ``simp``. The simplifier
will loop if you apply it blindly, but ``rewrite`` will do the trick.

.. code-block:: lean

    namespace hidden
    open nat

    def div : ℕ → ℕ → ℕ
    | x y :=
      if h : 0 < y ∧ y ≤ x then
        have x - y < x,
          from sub_lt (lt_of_lt_of_le h.left h.right) h.left,
        div (x - y) y + 1
      else
        0

    -- BEGIN
    example (x y : ℕ) :
      div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 :=
    by rw [div]

    example (x y : ℕ) (h : 0 < y ∧ y ≤ x) :
      div x y = div (x - y) y + 1 :=
    by rw [div, if_pos h]
    -- END

    end hidden

The following example is similar: it converts any natural number to a
binary expression, represented as a list of 0's and 1's. We have to
provide the equation compiler with evidence that the recursive call is
decreasing, which we do here with a ``sorry``. The ``sorry`` does not
prevent the bytecode evaluator from evaluating the function
successfully.

.. code-block:: lean

    def nat_to_bin : ℕ → list ℕ
    | 0       := [0]
    | 1       := [1]
    | (n + 2) :=
      have (n + 2) / 2 < n + 2, from sorry,
      nat_to_bin ((n + 2) / 2) ++ [n % 2]

    #eval nat_to_bin 1234567

As a final example, we observe that Ackermann's function can be
defined directly, because it is justified by the well foundedness of
the lexicographic order on the natural numbers.

.. code-block:: lean

    def ack : nat → nat → nat
    | 0     y     := y+1
    | (x+1) 0     := ack x 1
    | (x+1) (y+1) := ack x (ack (x+1) y)

    #eval ack 3 5

Lean's mechanisms for guessing a well-founded relation and then
proving that recursive calls decrease are still in a rudimentary
state. They will be improved over time. When they work, they provide a
much more convenient way of defining functions than using
``WellFounded.fix`` manually. When they don't, the latter is always
available as a backup.

.. TO DO: eventually, describe using_well_founded.

.. _nested_and_mutual_recursion:

<a name="_nested_and_mutual_recursion"></a> Mutual Recursion
----------------

**TODO: waiting for well-founded support in Lean 4**

Lean also supports mutual recursive definitions. The syntax is similar to that for mutual inductive types, as described in :numref:`mutual_and_nested_inductive_types`. Here is an example:

.. code-block:: lean

    mutual def even, odd
    with even : nat → bool
    | 0     := tt
    | (a+1) := odd a
    with odd : nat → bool
    | 0     := ff
    | (a+1) := even a

    example (a : nat) : even (a + 1) = odd a :=
    by simp [even]

    example (a : nat) : odd (a + 1) = even a :=
    by simp [odd]

    lemma even_eq_not_odd : ∀ a, even a = bnot (odd a) :=
    begin
      intro a, induction a,
      simp [even, odd],
      simp [*, even, odd]
    end

What makes this a mutual definition is that ``even`` is defined recursively in terms of ``odd``, while ``odd`` is defined recursively in terms of ``even``. Under the hood, this is compiled as a single recursive definition. The internally defined function takes, as argument, an element of a sum type, either an input to ``even``, or an input to ``odd``. It then returns an output appropriate to the input. To define that function, Lean uses a suitable well-founded measure. The internals are meant to be hidden from users; the canonical way to make use of such definitions is to use ``rewrite`` or ``simp``, as we did above.

Mutual recursive definitions also provide natural ways of working with mutual and nested inductive types, as described in :numref:`mutual_and_nested_inductive_types`. Recall the definition of ``even`` and ``odd`` as mutual inductive predicates, as presented as an example there:

.. code-block:: lean

    mutual inductive even, odd
    with even : ℕ → Prop
    | even_zero : even 0
    | even_succ : ∀ n, odd n → even (n + 1)
    with odd : ℕ → Prop
    | odd_succ : ∀ n, even n → odd (n + 1)

The constructors, ``even_zero``, ``even_succ``, and ``odd_succ`` provide positive means for showing that a number is even or odd. We need to use the fact that the inductive type is generated by these constructors to know that the zero is not odd, and that the latter two implications reverse. As usual, the constructors are kept in a namespace that is named after the type being defined, and the command ``open even odd`` allows us to access them move conveniently.

.. code-block:: lean

    mutual inductive even, odd
    with even : ℕ → Prop
    | even_zero : even 0
    | even_succ : ∀ n, odd n → even (n + 1)
    with odd : ℕ → Prop
    | odd_succ : ∀ n, even n → odd (n + 1)

    -- BEGIN
    open even odd

    theorem not_odd_zero : ¬ odd 0.

    mutual theorem even_of_odd_succ, odd_of_even_succ
    with even_of_odd_succ : ∀ n, odd (n + 1) → even n
    | _ (odd_succ n h) := h
    with odd_of_even_succ : ∀ n, even (n + 1) → odd n
    | _ (even_succ n h) := h
    -- END

For another example, suppose we use a nested inductive type to define a set of terms inductively, so that a term is either a constant (with a name given by a string), or the result of applying a constant to a list of constants.

.. code-block:: lean

    inductive term
    | const : string → term
    | app   : string → list term → term

We can then use a mutual recursive definition to count the number of constants occurring in a term, as well as the number occurring in a list of terms.

.. code-block:: lean

    inductive term
    | const : string → term
    | app   : string → list term → term

    -- BEGIN
    open term

    mutual def num_consts, num_consts_lst
    with num_consts : term → nat
    | (term.const n)  := 1
    | (term.app n ts) := num_consts_lst ts
    with num_consts_lst : list term → nat
    | []      := 0
    | (t::ts) := num_consts t + num_consts_lst ts

    def sample_term := app "f" [app "g" [const "x"], const "y"]

    #eval num_consts sample_term
    -- END


依赖模式匹配
--------------------------

All the examples of pattern matching we considered in
:numref:`pattern_matching` can easily be written using ``cases_on``
and ``rec_on``. However, this is often not the case with indexed
inductive families such as ``vector α n``, since case splits impose
constraints on the values of the indices. Without the equation
compiler, we would need a lot of boilerplate code to define very
simple functions such as ``map``, ``zip``, and ``unzip`` using
recursors. To understand the difficulty, consider what it would take
to define a function ``tail`` which takes a vector
``v : vector α (succ n)`` and deletes the first element. A first thought might be to
use the ``casesOn`` function:

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

#check @Vector.casesOn
/-
  {α : Type u}
  → {motive : (a : Nat) → Vector α a → Sort v} →
  → {a : Nat} → (t : Vector α a)
  → motive 0 nil
  → ((a : α) → {n : Nat} → (a_1 : Vector α n) → motive (n + 1) (cons a a_1))
  → motive a t
-/

end Vector
```

But what value should we return in the ``nil`` case? Something funny
is going on: if ``v`` has type ``Vector α (succ n)``, it *can't* be
nil, but it is not clear how to tell that to ``casesOn``.

One solution is to define an auxiliary function:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl
# end Vector
```

In the ``nil`` case, ``m`` is instantiated to ``0``, and
``noConfusion`` makes use of the fact that ``0 = succ n`` cannot
occur.  Otherwise, ``v`` is of the form ``a :: w``, and we can simply
return ``w``, after casting it from a vector of length ``m`` to a
vector of length ``n``.

The difficulty in defining ``tail`` is to maintain the relationships between the indices.
The hypothesis ``e : m = n + 1`` in ``tailAux`` is used to communicate the relationship
between ``n`` and the index associated with the minor premise.
Moreover, the ``zero = n + 1`` case is unreachable, and the canonical way to discard such
a case is to use ``noConfusion``.

The ``tail`` function is, however, easy to define using recursive
equations, and the equation compiler generates all the boilerplate
code automatically for us. Here are a number of similar examples:


```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def head : {n : Nat} → Vector α (n+1) → α
  | n, cons a as => a

def tail : {n : Nat} → Vector α (n+1) → Vector α n
  | n, cons a as => as

theorem eta : ∀ {n : Nat} (v : Vector α (n+1)), cons (head v) (tail v) = v
  | n, cons a as => rfl

def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : {n : Nat} → Vector α n → Vector β n → Vector (α × β) n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a, b) (zip as bs)
# end Vector
```

Note that we can omit recursive equations for "unreachable" cases such
as ``head nil``. The automatically generated definitions for indexed
families are far from straightforward. For example:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

#print map
#print map.match_1
# end Vector
```

The ``map`` function is even more tedious to define by hand than the
``tail`` function. We encourage you to try it, using ``recOn``,
``casesOn`` and ``noConfusion``.

<a name="_inaccessible_patterns"></a>Inaccessible Patterns
------------------

Sometimes an argument in a dependent matching pattern is not essential
to the definition, but nonetheless has to be included to specialize
the type of the expression appropriately. Lean allows users to mark
such subterms as *inaccessible* for pattern matching. These
annotations are essential, for example, when a term occurring in the
left-hand side is neither a variable nor a constructor application,
because these are not suitable targets for pattern matching. We can
view such inaccessible patterns as "don't care" components of the
patterns. You can declare a subterm inaccessible by writing
``.(t)``. If the inaccessible pattern can be inferred, you can also write
``_``.

The following example, we declare an inductive type that defines the
property of "being in the image of ``f``". You can view an element of
the type ``ImageOf f b`` as evidence that ``b`` is in the image of
``f``, whereby the constructor ``imf`` is used to build such
evidence. We can then define any function ``f`` with an "inverse"
which takes anything in the image of ``f`` to an element that is
mapped to it. The typing rules forces us to write ``f a`` for the
first argument, but this term is neither a variable nor a constructor
application, and plays no role in the pattern-matching definition. To
define the function ``inverse`` below, we *have to* mark ``f a``
inaccessible.

```lean
inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a
```

In the example above, the inaccessible annotation makes it clear that
``f`` is *not* a pattern matching variable.

Inaccessible patterns can be used to clarify and control definitions that
make use of dependent pattern matching. Consider the following
definition of the function ``Vector.add,`` which adds two vectors of
elements of a type, assuming that type has an associated addition
function:

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add as bs)

end Vector
```

The argument ``{n : Nat}`` appear after the colon, because it cannot
be held fixed throughout the definition.  When implementing this
definition, the equation compiler starts with a case distinction as to
whether the first argument is ``0`` or of the form ``n+1``.  This is
followed by nested case splits on the next two arguments, and in each
case the equation compiler rules out the cases are not compatible with
the first pattern.

But, in fact, a case split is not required on the first argument; the
``casesOn`` eliminator for ``Vector`` automatically abstracts this
argument and replaces it by ``0`` and ``n + 1`` when we do a case
split on the second argument. Using inaccessible patterns, we can prompt
the equation compiler to avoid the case split on ``n``

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector

def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | .(_),   nil,       nil       => nil
  | .(_), cons a as, cons b bs => cons (a + b) (add as bs)

# end Vector
```

Marking the position as an inaccessible pattern tells the
equation compiler first, that the form of the argument should be
inferred from the constraints posed by the other arguments, and,
second, that the first argument should *not* participate in pattern
matching.

The inaccessible pattern `.(_)` can be written as `_` for convenience.

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector

def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | _,   nil,       nil       => nil
  | _, cons a as, cons b bs => cons (a + b) (add as bs)

# end Vector
```

As we mentioned above, the argument ``{n : Nat}`` is part of the
pattern matching, because it cannot be held fixed throughout the
definition. In previous Lean versions, users often found it cumbersome
to have to include these extra discriminants. Thus, Lean 4
implements a new feature, *discriminant refinement*, which includes
these extra discriminants automatically for us.

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector

def add [Add α] {n : Nat} : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)

# end Vector
```

When combined with the *auto bound implicits* feature, you can simplify
the declare further and write:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector

def add [Add α] : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)

# end Vector
```

Using these new features, you can write the other vector functions defined
in the previous sections more compactly as follows:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def head : Vector α (n+1) → α
  | cons a as => a

def tail : Vector α (n+1) → Vector α n
  | cons a as => as

theorem eta : (v : Vector α (n+1)) → cons (head v) (tail v) = v
  | cons a as => rfl

def map (f : α → β → γ) : Vector α n → Vector β n → Vector γ n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : Vector α n → Vector β n → Vector (α × β) n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a, b) (zip as bs)
# end Vector
```

<a name="_match_expressions"></a>Match Expressions
-----------------

Lean also provides a compiler for *match-with* expressions found in
many functional languages.

```lean
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true
```

This does not look very different from an ordinary pattern matching
definition, but the point is that a ``match`` can be used anywhere in
an expression, and with arbitrary arguments.

```lean
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true

def filter (p : α → Bool) : List α → List α
  | []      => []
  | a :: as =>
    match p a with
    | true => a :: filter p as
    | false => filter p as

example : filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := rfl
```

Here is another example:

```lean
def foo (n : Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
      | 0,   true  => 0
      | m+1, true  => m + 7
      | 0,   false => 5
      | m+1, false => m + 3

#eval foo 7 true false

example : foo 7 true false = 9 := rfl
```

Lean uses the ``match`` construct internally to implement pattern-matching in all parts of the system.
Thus, all four of these definitions have the same net effect.

```lean
def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n

def bar₂ (p : Nat × Nat) : Nat :=
  match p with
  | (m, n) => m + n

def bar₃ : Nat × Nat → Nat :=
  fun (m, n) => m + n

def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n
```

These variations are equally useful for destructing propositions:

```lean
variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
 | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩


example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀
  let ⟨y, qy⟩ := h₁
  ⟨x, y, px, qy⟩
```

Local recursive declarations
---------

You can define local recursive declarations using the `let rec` keyword.

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop
-- {α : Type} → α → Nat → List α → List α
```

Lean creates an auxiliary declaration for each `let rec`. In the example above,
it created the declaration `replicate.loop` for the `let rec loop` occurring at `replicate`.
Note that, Lean "closes" the declaration by adding any local variable occurring in the
`let rec` declaration as additional parameters. For example, the local variable `a` occurs
at `let rec loop`.

You can also use `let rec` in tactic mode and for creating proofs by induction.

```lean
# def replicate (n : Nat) (a : α) : List α :=
#  let rec loop : Nat → List α → List α
#    | 0,   as => as
#    | n+1, as => loop n (a::as)
#  loop n []
theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
  exact aux n []
```

You can also introduce auxiliary recursive declarations using `where` clause after your definition.
Lean converts them into a `let rec`.

```lean
def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
```

Exercises
---------

1. Open a namespace ``Hidden`` to avoid naming conflicts, and use the
   equation compiler to define addition, multiplication, and
   exponentiation on the natural numbers. Then use the equation
   compiler to derive some of their basic properties.

2. Similarly, use the equation compiler to define some basic
   operations on lists (like the ``reverse`` function) and prove
   theorems about lists by induction (such as the fact that
   ``reverse (reverse xs) = xs`` for any list ``xs``).

3. Define your own function to carry out course-of-value recursion on
   the natural numbers. Similarly, see if you can figure out how to
   define ``WellFounded.fix`` on your own.

4. Following the examples in [Section Dependent Pattern Matching](#dependent_pattern_matching),
   define a function that will append two vectors.
   This is tricky; you will have to define an auxiliary function.

5. Consider the following type of arithmetic expressions. The idea is
   that ``var n`` is a variable, ``vₙ``, and ``const n`` is the
   constant whose value is ``n``.

```lean
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))
```

Here ``sampleExpr`` represents ``(v₀ * 7) + (2 * v₁)``.

Write a function that evaluates such an expression, evaluating each ``var n`` to ``v n``.

```lean
# inductive Expr where
#   | const : Nat → Expr
#   | var : Nat → Expr
#   | plus : Expr → Expr → Expr
#   | times : Expr → Expr → Expr
#   deriving Repr
# open Expr
# def sampleExpr : Expr :=
#   plus (times (var 0) (const 7)) (times (const 2) (var 1))
def eval (v : Nat → Nat) : Expr → Nat
  | const n     => sorry
  | var n       => v n
  | plus e₁ e₂  => sorry
  | times e₁ e₂ => sorry

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
-- #eval eval sampleVal sampleExpr
```

Implement "constant fusion," a procedure that simplifies subterms like
``5 + 7`` to ``12``. Using the auxiliary function ``simpConst``,
define a function "fuse": to simplify a plus or a times, first
simplify the arguments recursively, and then apply ``simpConst`` to
try to simplify the result.

```lean
# inductive Expr where
#   | const : Nat → Expr
#   | var : Nat → Expr
#   | plus : Expr → Expr → Expr
#   | times : Expr → Expr → Expr
#   deriving Repr
# open Expr
# def eval (v : Nat → Nat) : Expr → Nat
#   | const n     => sorry
#   | var n       => v n
#   | plus e₁ e₂  => sorry
#   | times e₁ e₂ => sorry
def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr := sorry

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e :=
  sorry

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  sorry
```

The last two theorems show that the definitions preserve the value.
