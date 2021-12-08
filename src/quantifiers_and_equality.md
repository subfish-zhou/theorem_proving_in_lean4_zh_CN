量词与等价
========================

上一章介绍了构造包含命题连接词的陈述证明的方法。在本章中，我们扩展了逻辑结构的功能，包括全称量词和存在量词，以及等价关系。

全称量词
------------------------

如果``α``是任何类型，我们可以将``α``上的一元谓词``p``作为``α → Prop``类型的对象。在这种情况下，给定``x : α``， ``p x``表示断言``p``在``x``上成立。类似地，一个对象``r : α → α → Prop``表示``α``上的二元关系：给定``x y : α``，``r x y``表示断言``x``与``y``相关。

全称量词``∀ x : α, p x``表示，对于每一个``x : α``，``p x``成立。与命题连接词一样，在自然演绎系统中，“forall”有引入和消去规则。非正式地，引入规则是：

> 给定``p x``的证明，在``x : α``是任意的情况下，我们得到``∀ x : α, p x``的证明。

消去规则是：

> 给定``∀ x : α, p x``的证明和任何项``t : α``，我们得到``p t``的证明。

与蕴含的情况一样，命题即类型。回想依赖箭头类型的引入规则:

> 给定类型为``β x``的项``t``，在``x : α``是任意的情况下，我们有``(fun x : α => t) : (x : α) → β x``。

消去规则：

> 给定项``s : (x : α) → β x``和任何项``t : α``，我们有``s t : β t``。

在``p x``具有``Prop``类型的情况下，如果我们用``∀ x : α, p x``替换``(x : α) → β x``，就得到构建涉及全称量词的证明的规则。

因此，构造演算用forall表达式来识别依赖箭头类型。如果``p``是任何表达式，``∀ x : α, p``不过是``(x : α) → p``的替代符号，在``p``是命题的情况下，前者比后者更自然。通常，表达式``p``取决于``x : α``。回想一下，在普通函数空间中，我们可以将``α → β``解释为``(x : α) → β``的特殊情况，其中``β``不依赖于``x``。类似地，我们可以把命题之间的蕴涵``p → q``看作是``∀ x : p, q``的特殊情况，其中``q``不依赖于``x``。

下面是一个例子，说明了如何运用命题即类型对应规则。

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left
```

作为一种符号约定，我们给予全称量词尽可能最宽的范围，因此上面例子中的假设中，需要用括号将``x``上的量词限制起来。证明``∀ y : α, p y``的标准方法是取任意的``y``，然后证明``p y``。这是引入规则。现在，给定``h``有类型``∀ x : α, p x ∧ q x``，表达式``h y``有类型``p y ∧ q y``。这是消去规则。取合取的左侧得到想要的结论``p y``。

只有约束变量名称不同的表达式被认为是等价的。因此，例如，我们可以在假设和结论中使用相同的变量``x``，并在证明中用不同的变量``z``实例化它:

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x  :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)
```

再举一个例子，下面是关系``r``的传递性：

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc
```

当我们在值``a b c``上实例化``trans_r``时，我们最终得到``r a b → r b c → r a c``的证明。将此应用于“假设”``hab : r a b``，我们得到了``r b c → r a c``的一个证明。最后将它应用到假设``hbc``中，得到结论``r a c``的证明。

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc
```

优点是我们可以简单地写``trans_r hab hbc``作为``r a c``的证明。一个缺点是Lean没有足够的信息来推断表达式``trans_r``和``trans_r hab``中的参数类型。第一个``#check``命令的输出是``r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3``，表示在本例中隐式参数未指定。

下面是一个用等价关系进行基本推理的例子:

```lean
variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd
```

为了习惯使用全称量词，你应该尝试本节末尾的一些练习。

依赖箭头类型的类型规则，特别是全称量词，将``Prop``与其他类型区分开来。假设我们有``α : Sort i``和``β : Sort j``，其中表达式``β``可能依赖于变量``x : α``。那么``(x : α) → β``是``Sort (imax i j)``的一个元素，其中``imax i j``是``i``和``j``在``j``不为0时的最大值，否则为0。

其想法如下。如果``j``不是``0``，然后``(x : α) → β``是``Sort (max i j)``类型的一个元素。换句话说，从``α``到``β``的一类依赖函数存在于指数为``i``和``j``最大值的宇宙中。然而，假设``β``属于``Sort 0``，即``Prop``的一个元素。在这种情况下，``(x : α) → β``也是``Sort 0``的一个元素，无论``α``生活在哪种类型的宇宙中。换句话说，如果``β``是一个依赖于``α``的命题，那么``∀ x : α, β``又是一个命题。这反映了``Prop``作为一种命题类型而不是数据类型的解释，这也使得``Prop``具有“非直谓性”。

“直谓性”一词起源于20世纪初的基础发展，当时逻辑学家如庞加莱和罗素将集合论的悖论归咎于“恶性循环”：当我们通过量化一个集合来定义一个属性时，这个集合包含了被定义的属性。注意，如果``α``是任何类型，我们可以在``α``上形成所有谓词的类型``α → Prop``(``α``的“幂”类型)。Prop的非直谓性意味着我们可以通过``α → Prop``形成量化命题。特别是，我们可以通过量化所有关于``α``的谓词来定义``α``上的谓词，这正是曾经被认为有问题的循环类型。

等价
--------

现在让我们来看看在Lean库中定义的最基本的关系之一，即等价关系。在[归纳类型](inductive_types.md)一章中，我们将解释如何从Lean的逻辑框架中定义等价。在这里我们解释如何使用它。

等价关系的基本性质：反身性、对称性、传递性。

```lean
#check Eq.refl    -- ∀ (a : ?m.1), a = a
#check Eq.symm    -- ?m.2 = ?m.3 → ?m.3 = ?m.2
#check Eq.trans   -- ?m.2 = ?m.3 → ?m.3 = ?m.4 → ?m.2 = ?m.4
```

通过告诉Lean不要插入隐式参数(在这里显示为元变量)，我们可以使输出更容易阅读。

```lean
universe u

#check @Eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u}  -- ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
```

``.{u}``告诉Lean实例化宇宙``u``上的常量。

因此，我们可以将上一节中的示例具体化为等价关系:

```lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```

我们也可以使用投影符号：

```lean
example : a = d := (hab.trans hcb.symm).trans hcd
```

反身性比它看起来更强大。回想一下，在构造演算中，项有一个计算解释，逻辑框架将可以简化为相同形式的项视为相同的。因此，一些非平凡的恒等式可以通过自反性来证明：

```lean
variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : α) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
```

框架的这个特性非常重要，以至于库中为``Eq.refl _``专门定义了一个符号``rfl``：

```lean
variable (α β : Type)
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : α) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl
```

然而，等价不仅仅是一种关系。它有一个重要的性质，即每个断言都遵从等价性，即我们可以在不改变真值的情况下对表达式做等价代换。也就是说，给定``h1 : a = b``和``h2 : p a``，我们可以构造一个证明``p b``，只需要使用代换``Eq.subst h1 h2``。

```lean
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```

第二个演示中的三角形是建立在``Eq.subst``和``Eq.symm``之上的宏，它可以通过``\t``来输入。

规则``Eq.subst``定义了一些辅助规则，用来执行更显式的替换。它们是为处理应用型项，即形式为``s t``的项而设计的。这些辅助规则是，使用``congrArg``来替换参数，使用``congrFun``来替换正在应用的项，并且可以同时使用``congr``来替换两者。

```lean
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁
```

Lean的库包含大量通用的等式，例如：

```lean
variable (a b c d : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
```

``Nat.mul_add``和``Nat.add_mul``是``Nat.left_distrib``和``Nat.right_distrib``的代称。上面的属性是为自然数类型``Nat``声明的。

这是一个使用代换以及结合律、交换律和分配律的自然数计算的例子。

```lean
example (x y z : Nat) : x * (y + z) = x * y + x * z := Nat.mul_add x y z
example (x y z : Nat) : (x + y) * z = x * z + y * z := Nat.add_mul x y z
example (x y z : Nat) : x + y + z = x + (y + z) := Nat.add_assoc x y z

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
```

注意，``Eq.subst``的第二个隐式参数提供了将要发生代换的表达式上下文，其类型为``α → Prop``。因此，推断这个谓词需要一个*高阶合一*（higher-order unification）的实例。一般来说，确定高阶合一器是否存在的问题是无法确定的，而Lean充其量只能提供不完美的和近似的解决方案。因此，``Eq.subst``并不总是做你想要它做的事。宏``h ▸ e``使用了更有效的启发式方法来计算这个隐参数，并且在不能应用``Eq.subst``的情况下通常会成功。

因为等式推理是如此普遍和重要，Lean提供了许多机制来更有效地执行它。下一节将提供允许你以更自然和清晰的方式编写计算式证明的语法。但更重要的是，等式推理是由项重写器、简化器和其他种类的自动化方法支持的。术语重写器和简化器将在下一节中简要描述，然后在下一章中更详细地描述。

计算式证明
--------------------

一个计算式证明只是一个中间结果的链，这意味着由基本原则，如平等的传递性组成。在Lean中，计算证明从关键字``calc``开始，语法如下:
A calculational proof is just a chain of intermediate results that are
meant to be composed by basic principles such as the transitivity of
equality. In Lean, a calculation proof starts with the keyword
``calc``, and has the following syntax:

```
calc
  <expr>_0  'op_1'  <expr>_1  ':='  <proof>_1
    '_'     'op_2'  <expr>_2  ':='  <proof>_2
     ...
    '_'     'op_n'  <expr>_n  ':='  <proof>_n

```

Each ``<proof>_i`` is a proof for ``<expr>_{i-1} op_i <expr>_i``.

Here is an example:

```lean
variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4
```

The style of writing proofs is most effective when it is used in
conjunction with the ``simp`` and ``rewrite`` tactics, which are
discussed in greater detail in the next chapter. For example, using
the abbreviation ``rw`` for rewrite, the proof above could be written
as follows:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ =  e     := by rw [h4]
```

Essentially, the ``rw`` tactic uses a given equality (which can be a
hypothesis, a theorem name, or a complex term) to "rewrite" the
goal. If doing so reduces the goal to an identity ``t = t``, the
tactic applies reflexivity to prove it.

Rewrites can be applied sequentially, so that the proof above can be
shortened to this:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ =  e     := by rw [h4]
```

Or even this:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]
```

The ``simp`` tactic, instead, rewrites the goal by applying the given
identities repeatedly, in any order, anywhere they are applicable in a
term. It also uses other rules that have been previously declared to
the system, and applies commutativity wisely to avoid looping. As a
result, we can also prove the theorem as follows:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
```

We will discuss variations of ``rw`` and ``simp`` in the next chapter.

The ``calc`` command can be configured for any relation that supports
some form of transitivity. It can even combine different relations.

```lean
example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3
```

With ``calc``, we can write the proof in the last section in a more
natural and perspicuous way.

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
        _ = x * x + y * x + (x + y) * y            := by rw [Nat.add_mul]
        _ = x * x + y * x + (x * y + y * y)        := by rw [Nat.add_mul]
        _ = x * x + y * x + x * y + y * y          := by rw [←Nat.add_assoc]
```

Here the left arrow before ``Nat.add_assoc`` tells rewrite to use the
identity in the opposite direction. (You can enter it with ``\l`` or
use the ascii equivalent, ``<-``.) If brevity is what we are after,
both ``rw`` and ``simp`` can do the job on their own:

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm]
```

The Existential Quantifier
--------------------------

Finally, consider the existential quantifier, which can be written as
either ``exists x : α, p x`` or ``∃ x : α, p x``.  Both versions are
actually notationally convenient abbreviations for a more long-winded
expression, ``Exists (fun x : α => p x)``, defined in Lean's library.

As you should by now expect, the library includes both an introduction
rule and an elimination rule. The introduction rule is
straightforward: to prove ``∃ x : α, p x``, it suffices to provide a
suitable term ``t`` and a proof of ``p t``. Here are some examples:

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro
```

We can use the anonymous constructor notation ``⟨t, h⟩`` for
``Exists.intro t h``, when the type is clear from the context.

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩
```

Note that ``Exists.intro`` has implicit arguments: Lean has to infer
the predicate ``p : α → Prop`` in the conclusion ``∃ x, p x``.  This
is not a trivial affair. For example, if we have have
``hg : g 0 0 = 0`` and write ``Exists.intro 0 hg``, there are many possible values
for the predicate ``p``, corresponding to the theorems ``∃ x, g x x = x``,
``∃ x, g x x = 0``, ``∃ x, g x 0 = x``, etc. Lean uses the
context to infer which one is appropriate. This is illustrated in the
following example, in which we set the option ``pp.explicit`` to true
to ask Lean's pretty-printer to show the implicit arguments.

```lean
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4
```

We can view ``Exists.intro`` as an information-hiding operation, since
it hides the witness to the body of the assertion. The existential
elimination rule, ``Exists.elim``, performs the opposite operation. It
allows us to prove a proposition ``q`` from ``∃ x : α, p x``, by
showing that ``q`` follows from ``p w`` for an arbitrary value
``w``. Roughly speaking, since we know there is an ``x`` satisfying
``p x``, we can give it a name, say, ``w``. If ``q`` does not mention
``w``, then showing that ``q`` follows from ``p w`` is tantamount to
showing the ``q`` follows from the existence of any such ``x``. Here
is an example:

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
```

It may be helpful to compare the exists-elimination rule to the
or-elimination rule: the assertion ``∃ x : α, p x`` can be thought of
as a big disjunction of the propositions ``p a``, as ``a`` ranges over
all the elements of ``α``. Note that the anonymous constructor
notation ``⟨w, hw.right, hw.left⟩`` abbreviates a nested constructor
application; we could equally well have written ``⟨w, ⟨hw.right, hw.left⟩⟩``.

Notice that an existential proposition is very similar to a sigma
type, as described in dependent types section.  The difference is that
given ``a : α`` and ``h : p a``, the term ``Exists.intro a h`` has
type ``(∃ x : α, p x) : Prop`` and ``Sigma.mk a h`` has type
``(Σ x : α, p x) : Type``. The similarity between ``∃`` and ``Σ`` is another
instance of the Curry-Howard isomorphism.

Lean provides a more convenient way to eliminate from an existential
quantifier with the ``match`` expression:

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
```

The ``match`` expression is part of Lean's function definition system,
which provides convenient and expressive ways of defining complex
functions.  Once again, it is the Curry-Howard isomorphism that allows
us to co-opt this mechanism for writing proofs as well.  The ``match``
statement "destructs" the existential assertion into the components
``w`` and ``hw``, which can then be used in the body of the statement
to prove the proposition. We can annotate the types used in the match
for greater clarity:

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩
```

We can even use the match statement to decompose the conjunction at the same time:

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

Lean also provides a pattern-matching ``let`` expression:

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
```

This is essentially just alternative notation for the ``match``
construct above. Lean will even allow us to use an implicit ``match``
in the ``fun`` expression:

```lean
# variable (α : Type) (p q : α → Prop)
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

We will see in [Chapter Induction and Recursion](./induction_and_recursion.md) that all these variations are
instances of a more general pattern-matching construct.

In the following example, we define ``even a`` as ``∃ b, a = 2*b``,
and then we show that the sum of two even numbers is an even number.

```lean
def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc
        a + b = 2 * w1 + 2 * w2  := by rw [hw1, hw2]
          _   = 2*(w1 + w2)      := by rw [Nat.mul_add])))
```

Using the various gadgets described in this chapter --- the match
statement, anonymous constructors, and the ``rewrite`` tactic, we can
write this proof concisely as follows:

```lean
# def is_even (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
```

Just as the constructive "or" is stronger than the classical "or," so,
too, is the constructive "exists" stronger than the classical
"exists". For example, the following implication requires classical
reasoning because, from a constructive standpoint, knowing that it is
not the case that every ``x`` satisfies ``¬ p`` is not the same as
having a particular ``x`` that satisfies ``p``.

```lean
open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x :=  ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)
```

What follows are some common identities involving the existential
quantifier. In the exercises below, we encourage you to prove as many
as you can. We also leave it to you to determine which are
nonconstructive, and hence require some form of classical reasoning.

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
```

Notice that the second example and the last two examples require the
assumption that there is at least one element ``a`` of type ``α``.

Here are solutions to two of the more difficult ones:

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (a : α)
variable (r : Prop)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from  hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))
```

More on the Proof Language
--------------------------

We have seen that keywords like ``fun``, ``have``, and ``show`` make
it possible to write formal proof terms that mirror the structure of
informal mathematical proofs. In this section, we discuss some
additional features of the proof language that are often convenient.

To start with, we can use anonymous "have" expressions to introduce an
auxiliary goal without having to label it. We can refer to the last
expression introduced in this way using the keyword ``this``:

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)
```

Often proofs move from one fact to the next, so this can be effective
in eliminating the clutter of lots of labels.

When the goal can be inferred, we can also ask Lean instead to fill in
the proof by writing ``by assumption``:

```lean
# variable (f : Nat → Nat)
# variable (h : ∀ x : Nat, f x ≤ f (x + 1))
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)
```

This tells Lean to use the ``assumption`` tactic, which, in turn,
proves the goal by finding a suitable hypothesis in the local
context. We will learn more about the ``assumption`` tactic in the
next chapter.

We can also ask Lean to fill in the proof by writing ``‹p›``, where
``p`` is the proposition whose proof we want Lean to find in the
context.  You can type these corner quotes using ``\f<`` and ``\f>``,
respectively. The letter "f" is for "French," since the unicode
symbols can also be used as French quotation marks. In fact, the
notation is defined in Lean as follows:

```lean
notation "‹" p "›" => show p by assumption
```

This approach is more robust than using ``by assumption``, because the
type of the assumption that needs to be inferred is given
explicitly. It also makes proofs more readable. Here is a more
elaborate example:

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
```

Keep in mind that you can use the French quotation marks in this way
to refer to *anything* in the context, not just things that were
introduced anonymously. Its use is also not limited to propositions,
though using it for data is somewhat odd:

```lean
example (n : Nat) : Nat := ‹Nat›
```

Later, we show how you can extend the proof language using the Lean macro system.

练习
---------

1. 证明以下等式：

```lean
 variable (α : Type) (p q : α → Prop)

 example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
 example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
 example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
```
你还应该想想为什么在最后一个例子中反过来是不能证明的。

2. 当一个公式的组成部分不依赖于被量化的变量时，通常可以把它提取出一个全称量词的范围。尝试证明这些(第二个命题中的一个方向需要经典逻辑)：

```lean
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
```

3. 考虑“理发师悖论”：在一个小镇里，这里有一个（男性）理发师给所有不为自己刮胡子的人刮胡子。证明这里存在矛盾：

```lean
variable (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false := sorry
```

4. 如果没有任何参数，类型``Prop``的表达式只是一个断言。填入下面``prime``和``Fermat_prime``的定义，并构造每个给定的断言。例如，通过断言每个自然数``n``都有一个大于``n``的质数，你可以说有无限多个质数。哥德巴赫弱猜想指出，每一个大于5的奇数都是三个素数的和。如果有必要，请查阅费马素数的定义或其他任何资料。

```lean
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry
```

5. 尽可能多地证明存在量词一节列出的等式。