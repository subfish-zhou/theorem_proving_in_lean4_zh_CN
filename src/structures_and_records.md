结构体和记录
======================

我们已经看到Lean的基本系统包括递归类型。此外，显然仅基于类型宇宙、依赖箭头类型和递归类型，就有可能构建一个坚实的数学大厦；其他的一切都是由此而来。Lean标准库包含许多递归类型的实例(例如，``Nat``，``Prod``，``List``)，甚至逻辑连接词也是使用递归类型定义的。

回忆一下，只包含一个构造子的非递归递归类型被称为*结构体*（structure）或*记录*（record）。乘积类型是一种结构体，依赖乘积(Sigma)类型也是如此。一般来说，每当我们定义一个结构体``S``时，我们通常定义*投影*（projection）函数来“析构”（destruct）``S``的每个实例并检索存储在其字段中的值。``prod.pr1``和``prod.pr2``，分别返回乘积对中的第一个和第二个元素的函数，就是这种投影的例子。

在编写程序或形式化数学时，定义包含许多字段的结构体是很常见的。Lean中可用``structure``命令实现此过程。当我们使用这个命令定义一个结构体时，Lean会自动生成所有的投影函数。``structure``命令还允许我们根据以前定义的结构体定义新的结构体。此外，Lean为定义给定结构体的实例提供了方便的符号。

## 声明结构体

结构体命令本质上是定义归纳数据类型的“前端”。每个``structure``声明都会引入一个同名的命名空间。一般形式如下:

```
    structure <name> <parameters> <parent-structures> where
      <constructor> :: <fields>
```

大多数部分不是必要的。例子：

```lean
structure Point (α : Type u) where
  mk :: (x : α) (y : α)
```

类型``Point``的值是使用``Point.mk a b``创建的，并且点``p``的字段可以使用``Point.x p``和``Point.y p``。结构体命令还生成有用的递归子和定理。下面是为上述声明生成的一些结构体方法。

```lean
# structure Point (α : Type u) where
#  mk :: (x : α) (y : α)
#check Point       -- a Type
#check @Point.rec  -- the eliminator
#check @Point.mk   -- the constructor
#check @Point.x    -- a projection
#check @Point.y    -- a projection
```

如果没有提供构造子名称，则默认的构造函数名为' ' mk ' '。如果在每个字段之间添加换行符，也可以避免字段名周围的括号。

```lean
structure Point (α : Type u) where
  x : α
  y : α
```

下面是一些使用生成的结构的简单定理和表达式。像往常一样，您可以通过使用命令``open Point``来避免前缀``Point``。

```lean
#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

open Point

example (a b : α) : x (mk a b) = a :=
  rfl

example (a b : α) : y (mk a b) = b :=
  rfl
```

给定``p : Point Nat``，符号``p.x``是``Point.x p``的缩写。这提供了一种方便的方式来访问结构体的字段。

```lean
def p := Point.mk 10 20

#check p.x  -- Nat
#eval p.x   -- 10
#eval p.y   -- 20
```

点表示法不仅方便于访问记录的投影，而且也方便于应用同名命名空间中定义的函数。回想一下[合取](./propositions_and_proofs.md#_conjunction)一节，如果``p``具有``Point``类型，那么表达式``p.foo``被解释为``Point.foo p``，假设``foo``的第一个非隐式参数具有类型``Point``，表达式``p.add q``因此是``Point.add p q``的缩写。可见下面的例子。

```lean
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4

#eval p.add q  -- {x := 4, y := 6}
```

在下一章中，您将学习如何定义一个像``add``这样的函数，这样它就可以通用地为``Point α``的元素工作，而不仅仅是``Point Nat``，只要假设``α``有一个关联的加法操作。

更一般地，给定一个表达式``p.foo x y z``其中`p : Point`，Lean会把``p``以``Point``为类型插入到``Point.foo``的第一个参数。例如，下面是标量乘法的定义，``p.smul 3``被解释为``Point.smul 3 p``。

```lean
def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p : Point Nat := Point.mk 1 2

#eval p.smul 3  -- {x := 3, y := 6}
```

对``List.map``函数使用类似的技巧很常用。它接受一个列表作为它的第二个非隐式参数:

```lean
#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

#eval xs.map f  -- [1, 4, 9]
```

此处``xs.map f``被解释为``List.map f xs``。

Here ``xs.map f`` is interpreted as ``List.map f xs``.

对象
-------

我们一直在使用构造子创建结构体类型的元素。对于包含许多字段的结构，这通常是不方便的，因为我们必须记住字段定义的顺序。因此，Lean为定义结构体类型的元素提供了以下替代符号。

```
    { (<field-name> := <expr>)* : structure-type }
    or
    { (<field-name> := <expr>)* }
```

只要可以从期望的类型推断出结构体的名称，后缀``: structure-type``就可以省略。例如，我们使用这种表示法来定义“点”。字段的指定顺序无关紧要，因此下面的所有表达式定义相同的点。

```lean
structure Point (α : Type u) where
  x : α
  y : α

#check { x := 10, y := 20 : Point Nat }  -- Point ℕ
#check { y := 20, x := 10 : Point _ }
#check ({ x := 10, y := 20 } : Point Nat)

example : Point Nat :=
  { y := 20, x := 10 }
```

如果一个字段的值没有指定，Lean会尝试推断它。如果不能推断出未指定的字段，Lean会标记一个错误，表明相应的占位符无法合成。

```lean
structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β

#check { a := 10, b := true : MyStruct }
```

*记录更新*是另一个常见的操作，相当于通过修改旧记录中的一个或多个字段的值来创建一个新的记录对象。通过在字段赋值之前添加注释``s with``，Lean允许您指定记录规范中未赋值的字段，该字段应从之前定义的结构对象``s``中获取。如果提供了多个记录对象，那么将按顺序访问它们，直到Lean找到一个包含未指定字段的记录对象。如果在访问了所有对象之后仍未指定任何字段名，Lean将引发错误。

```lean
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }
#eval { p with x := 4 }  -- { x := 4, y := 2 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point3 Nat :=
  { p, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl
```

继承
-----------

我们可以通过添加新的字段来*扩展*现有的结构体。这个特性允许我们模拟一种形式的*继承*。

```lean
structure Point (α : Type u) where
  x : α
  y : α

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color
```

在下一个例子中，我们使用多重继承定义一个结构体，然后使用父结构的对象定义一个对象。

```lean
structure Point (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RGBValue where
  no_blue : blue = 0

def p : Point Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl
```