命题和证明
=======================

前一章你已经看到了在Lean中定义对象和函数的一些方法。在本章中，我们还将开始解释如何用依值类型论的语言来编写数学命题和证明。

## 命题即类型

证明在依值类型论语言中定义的对象的断言（assertion）的一种策略是在定义语言之上分层断言语言和证明语言。但是，没有理由以这种方式重复使用多种语言：依值类型论是灵活和富有表现力的，我们也没有理由不能在同一个总框架中表示断言和证明。

例如，我们可引入一种新类型``Prop``，来表示命题，然后引入用其他命题构造新命题的构造子。

```lean
def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop
```

对每个元素``p : Prop``，可以引入另一个类型``Proof p``，作为``p``的证明的类型。“公理”是这个类型中的常值。

```lean
structure Proof (p : Prop) : Type where
  proof : p
#check Proof   -- Proof : Prop → Type

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm p q     -- Proof (Implies (And p q) (And q p))
```

然而，除了公理之外，我们还需要从旧证明中建立新证明的规则。例如，在许多命题逻辑的证明系统中，我们有肯定前件式（modus ponens）推理规则:

>  如果能证明``Implies p q``和``p``，则能证明``q``。

我们可以如下地表示它：

```lean
axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
```

命题逻辑的自然演绎系统通常也依赖于以下规则：

> 当假设``p``成立时，如果我们能证明``q``. 则我们能证明``Implies p q``.

我们可以如下地表示它：

```lean
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)
```

这个功能让我们可以合理地搭建断言和证明。确定表达式``t``是``p``的证明，只需检查``t``具有类型``Proof p``。

可以做一些简化。首先，我们可以通过将``Proof p``和``p``本身合并来避免重复地写``Proof``这个词。换句话说，只要我们有``p : Prop``，我们就可以把``p``解释为一种类型，也就是它的证明类型。然后我们可以把``t : p``读作``t``是``p``的证明。

此外，我们可以在``Implies p q``和``p → q``之间来回切换。换句话说，命题``p``和``q``之间的含义对应于一个函数，它将``p``的任何元素接受为``q``的一个元素。因此，引入连接词``Implies``是完全多余的：我们可以使用依值类型论中常见的函数空间构造子``p → q``作为我们的蕴含概念。

这是在构造演算（Calculus of Constructions）中遵循的方法，因此在Lean中也是如此。自然演绎证明系统中的蕴含规则与控制函数抽象（abstraction）和应用（application）的规则完全一致，这是*Curry-Howard同构*的一个实例，有时也被称为*命题即类型*。事实上，类型``Prop``是上一章描述的类型层次结构的最底部``Sort 0``的语法糖。此外，``Type u``也只是``Sort (u+1)``的语法糖。``Prop``有一些特殊的特性，但像其他类型宇宙一样，它在箭头构造子下是封闭的:如果我们有``p q : Prop``，那么``p → q : Prop``。

至少有两种将命题作为类型来思考的方法。对于那些对逻辑和数学中的构造主义者来说，这是对命题含义的忠实诠释：命题``p``代表了一种数据类型，即构成证明的数据类型的说明。``p``的证明就是正确类型的对象``t : p``。

非构造主义者可以把它看作是一种简单的编码技巧。对于每个命题``p``，我们关联一个类型，如果``p``为假，则该类型为空，如果``p``为真，则有且只有一个元素，比如``*``。在后一种情况中，让我们说(与之相关的类型)``p``被*占据*（inhabited）。恰好，函数应用和抽象的规则可以方便地帮助我们跟踪``Prop``的哪些元素是被占据的。所以构造一个元素``t : p``告诉我们``p``确实是正确的。你可以把``p``的占据者想象成“``p``为真”的事实。对``p → q``的证明使用“``p``是真的”这个事实来得到“``q``是真的”这个事实。

事实上，如果``p : Prop``是任何命题，那么Lean的内核将任意两个元素``t1 t2 : p``看作定义相等，就像它把``(fun x => t) s``和``t[s/x]``看作定义等价。这就是所谓的“证明无关性”（proof irrelevance）。这意味着，即使我们可以把证明``t : p``当作依值类型论语言中的普通对象，它们除了``p``是真的这一事实之外，没有其他信息。

我们所建议的思考“命题即类型”范式的两种方式在一个根本性的方面有所不同。从构造的角度看，证明是抽象的数学对象，它被依值类型论中的合适表达式所*表示*。相反，如果我们从上述编码技巧的角度考虑，那么表达式本身并不表示任何有趣的东西。相反，是我们可以写下它们并检查它们是否有良好的类型这一事实确保了有关命题是真的。换句话说，表达式*本身*就是证明。

在下面的论述中，我们将在这两种说话方式之间来回切换，有时说一个表达式“构造”或“产生”或“返回”一个命题的证明，有时则简单地说它“是”这样一个证明。这类似于计算机科学家偶尔会模糊语法和语义之间的区别，有时说一个程序“计算”某个函数，有时又说该程序“是”该函数。

为了用依值类型论的语言正式表达一个数学断言，我们需要展示一个项``p : Prop``。为了*证明*该断言，我们需要展示一个项``t : p``。Lean的任务，作为一个证明助手，是帮助我们构造这样一个项``t``，并验证它的格式是否良好，类型是否正确。

## 以“命题即类型”的方式工作

在“命题即类型”范式中，只涉及``→``的定理可以通过lambda抽象和应用来证明。在Lean中，``theorem``命令引入了一个新的定理：

```lean
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
```

这与上一章中常量函数的定义完全相同，唯一的区别是参数是``Prop``的元素，而不是``Type``的元素。直观地说，我们对``p → q → p``的证明假设``p``和``q``为真，并使用第一个假设(平凡地)建立结论``p``为真。

请注意，``theorem``命令实际上是``def``命令的一个翻版：在命题和类型对应下，证明定理``p → q → p``实际上与定义关联类型的元素是一样的。对于内核类型检查器，这两者之间没有区别。

然而，定义和定理之间有一些实用的区别。正常情况下，永远没有必要展开一个定理的“定义”；通过证明无关性，该定理的任何两个证明在定义上都是相等的。一旦一个定理的证明完成，通常我们只需要知道该证明的存在；证明是什么并不重要。鉴于这一事实，Lean将证明标记为*不可还原*（irreducible），作为对解析器（更确切地说，是*繁饰器*）的提示，在处理文件时一般不需要展开它。事实上，Lean通常能够并行地处理和检查证明，因为评估一个证明的正确性不需要知道另一个证明的细节。

和定义一样，``#print``命令可以展示一个定理的证明。

```lean
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

#print t1
```

注意，lambda抽象``hp : p``和``hq : q``可以被视为``t1``的证明中的临时假设。Lean还允许我们通过``show``语句明确指定最后一个项``hp``的类型。

```lean
theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp --试试改成 show q from hp 会怎样？
```

添加这些额外的信息可以提高证明的清晰度，并有助于在编写证明时发现错误。``show``命令只是注释类型，而且在内部，我们看到的所有关于``t1``的表示都产生了相同的项。

与普通定义一样，我们可以将lambda抽象的变量移到冒号的左边：

```lean
theorem t1 (hp : p) (hq : q) : p := hp

#print t1    -- p → q → p
```

现在我们可以把定理``t1``作为一个函数应用。

```lean
theorem t1 (hp : p) (hq : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1 hp
```

这里，``axiom``声明假定存在给定类型的元素，因此可能会破坏逻辑一致性。例如，我们可以使用它来假设空类型`False`有一个元素：

```lean
axiom unsound : False
-- false可导出一切
theorem ex : 1 = 0 :=
False.elim unsound
```

声明“公理”``hp : p``等同于声明``p``为真，正如``hp``所证明的那样。应用定理``t1 : p → q → p``到事实``hp : p``（也就是``p``为真）得到定理``t1 hp : q → p``。

回想一下，我们也可以这样写定理``t1``:

```lean
theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1
```

``t1``的类型现在是``∀ {p q : Prop}, p → q → p``。我们可以把它理解为“对于每一对命题``p q``，我们都有``p → q → p``”。例如，我们可以将所有参数移到冒号的右边：

```lean
theorem t1 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp
```

如果``p``和``q``被声明为变量，Lean会自动为我们推广它们:

```lean
variable {p q : Prop}

theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp
```

事实上，通过命题即类型的对应关系，我们可以声明假设``hp``为``p``，作为另一个变量:

```lean
variable {p q : Prop}
variable (hp : p)

theorem t1 : q → p := fun (hq : q) => hp
```

Lean检测到证明使用``hp``，并自动添加``hp : p``作为前提。在所有情况下，命令``#print t1``仍然会产生``∀ p q : Prop, p → q → p``。这个类型也可以写成``∀ (p q : Prop) (hp : p) (hq :q), p``，因为箭头仅仅表示一个箭头类型，其中目标不依赖于约束变量。

当我们以这种方式推广``t1``时，我们就可以将它应用于不同的命题对，从而得到一般定理的不同实例。

```lean
theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t1 p q                -- p → q → p
#check t1 r s                -- r → s → r
#check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t1 (r → s) (s → r) h  -- (s → r) → r → s
```

同样，使用命题即类型对应，类型为``r → s``的变量``h``可以看作是``r → s``存在的假设或前提。

作为另一个例子，让我们考虑上一章讨论的组合函数，现在用命题代替类型。

```lean
variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
fun h₃ : p =>
show r from h₁ (h₂ h₃)
```

作为一个命题逻辑定理，``t2``是什么意思？

注意，数字unicode下标输入方式为``\0``，``\1``，``\2``，...。

## 命题逻辑

Lean定义了所有标准的逻辑连接词和符号。命题连接词有以下表示法:

| Ascii      | Unicode   | 编辑器缩写                | 定义   |
|------------|-----------|--------------------------|--------|
| True       |           |                          | True   |
| False      |           |                          | False  |
| Not        | ¬         | ``\not``, ``\neg``       | Not    |
| /\\        | ∧        | ``\and``                 | And    |
| \\/        | ∨        | ``\or``                  | Or     |
| ->         | →         | ``\to``, ``\r``, ``\imp``|        |
| <->        | ↔         | ``\iff``, ``\lr``        | Iff    |

它们都接收``Prop``值。

```lean
variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p
```

操作符的优先级如下：``¬ > ∧ > ∨ > → > ↔``。举例：``a ∧ b → c ∨ d ∧ e``意为``(a ∧ b) → (c ∨ (d ∧ e))``。``→``等二元关系是右结合的。所以如果我们有``p q r : Prop``，表达式``p → q → r``读作“如果``p``，那么如果``q``，那么``r``”。这是``p ∧ q → r``的柯里化形式。

在上一章中，我们观察到lambda抽象可以被看作是``→``的“引入规则”，展示了如何“引入”或建立一个蕴含。应用可以看作是一个“消去规则”，展示了如何在证明中“消去”或使用一个蕴含。其他的命题连接词在Lean的库``Prelude.core``文件中定义。(参见[导入文件](./interacting_with_lean.md#_importing_files)以获得关于库层次结构的更多信息)，并且每个连接都带有其规范引入和消去规则。

### 合取

表达式``And.intro h1 h2``是``p ∧ q``的证明，它使用了``h1 : p``和``h2 : q``的证明。通常把``And.intro``称为*合取引入*规则。下面的例子我们使用``And.intro``来创建``p → q → p ∧ q``的证明。

```lean
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq
```

``example``命令声明了一个没有名字也不会永久保存的定理。本质上，它只是检查给定项是否具有指定的类型。它便于说明，我们将经常使用它。

表达式``And.left h``从``h : p ∧ q``建立了一个``p``的证明。类似地，``And.right h``是``q``的证明。它们常被称为左或右*合取消去*规则。

```lean
variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
```

我们现在可以证明``p ∧ q → q ∧ p``：

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
And.intro (And.right h) (And.left h)
```

请注意，引入和消去与笛卡尔积的配对和投影操作类似。区别在于，给定``hp : p``和``hq : q``，``And.intro hp hq``具有类型``p ∧ q : Prop``，而``Prod hp hq``具有类型``p × q : Type``。``∧``和``×``之间的相似性是Curry-Howard同构的另一个例子，但与蕴涵和函数空间构造子不同，在Lean中``∧``和``×``是分开处理的。然而，通过类比，我们刚刚构造的证明类似于交换一对中的元素的函数。

我们将在[结构体和记录](./structures_and_records.md)一章中看到Lean中的某些类型是*Structures*，也就是说，该类型是用单个规范的*构造子*定义的，该构造子从一系列合适的参数构建该类型的一个元素。对于每一组``p q : Prop``， ``p ∧ q``就是一个例子:构造一个元素的规范方法是将``And.intro``应用于合适的参数``hp : p``和``hq : q``。Lean允许我们使用*匿名构造子*表示法``⟨arg1, arg2, ...⟩``在此类情况下，当相关类型是归纳类型并可以从上下文推断时。特别地，我们经常可以写入``⟨hp, hq⟩``，而不是``And.intro hp hq``:

```lean
variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)
```

尖括号可以用``\<``和``\>``打出来。

Lean提供了另一个有用的语法小工具。给定一个归纳类型``Foo``的表达式``e``(可能应用于一些参数)，符号``e.bar``是``Foo.bar e``的缩写。这为访问函数提供了一种方便的方式，而无需打开名称空间。例如，下面两个表达的意思是相同的：

```lean
variable (xs : List Nat)

#check List.length xs
#check xs.length
```

给定``h : p ∧ q``，我们可以写``h.left``来表示``And.left h``以及``h.right``来表示``And.right h``。因此我们可以简写上面的证明如下：

```lean
variable (p q : Prop)
example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩
```

在简洁和含混不清之间有一条微妙的界限，以这种方式省略信息有时会使证明更难阅读。但对于像上面这样简单的结构，当``h``的类型和结构的目标很突出时，符号是干净和有效的。

像``And.``这样的迭代结构是很常见的。Lean还允许你将嵌套的构造函数向右结合，这样这两个证明是等价的:

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p ∧ q:=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q:=
  ⟨h.right, h.left, h.right⟩
```

这一点也很常用。

### 析取

表达式``Or.intro_left q hp``从证明``hp : p``建立了``p ∨ q``的证明。类似地，``Or.intro_right p hq``从证明``hq : q``建立了``p ∨ q``的证明。这是左右析取引入规则。

```lean
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
```
析取消去规则稍微复杂一点。这个想法是，我们可以从``p ∨ q``证明``r``，通过从``p``证明``r``，且从``q``证明``r``。换句话说，它是一种案例证明。在表达式``Or.elim hpq hpr hqr``中，``Or.elim``接受三个论证，``hpq : p ∨ q``，``hpr : p → r``和``hqr : q → r``，生成``r``的证明。在下面的例子中，我们使用``Or.elim``证明``p ∨ q → q ∨ p``。

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
     show q ∨ p from Or.intro_left p hq)
```

在大多数情况下，``Or.intro_right``和``Or.intro_left``的第一个参数可以由Lean自动推断出来。因此，Lean提供了``Or.inr``和``Or.inl``作为``Or.intro_right _``和``Or.intro_left _``的缩写。因此，上面的证明项可以写得更简洁:

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

Lean的完整表达式中有足够的信息来推断``hp``和``hq``的类型。但是在较长的版本中使用类型注释可以使证明更具可读性，并有助于捕获和调试错误。

因为``Or``有两个构造子，所以不能使用匿名构造子表示法。但我们仍然可以写``h.elim``而不是``Or.elim h``，不过你需要注意这些缩写是增强还是降低了可读性：

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

### 否定和假言

否定``¬p``真正的定义是``p → False``，所以我们通过从``p``导出一个矛盾来获得``¬p``。类似地，表达式``hnp hp``从``hp : p``和``hnp : ¬p``产生一个``False``的证明。下一个例子用所有这些规则来证明``(p → q) → ¬q → ¬p``。（``¬``符号可以由``\not``或者``\neg``来写出。）

```lean
variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)
```

连接词``False``只有一个消去规则``False.elim``，它表达了一个事实，即矛盾能导出一切。这个规则有时被称为*ex falso* 【*ex falso sequitur quodlibet*（无稽之谈）的缩写】，或*爆炸原理*。

```lean
variable (tp q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
```

假命题导出任意的事实``q``，是``False.elim``的一个隐参数，而且是自动推断出来的。这种从相互矛盾的假设中推导出任意事实的模式很常见，用``absurd``来表示。

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```

证明``¬p → q → (q → p) → r``：

```lean
variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp
```

顺便说一句，就像``False``只有一个消去规则，``True``只有一个引入规则``True.intro : true``。换句话说，``True``就是真，并且有一个标准证明``True.intro``。

### 逻辑等价

表达式``Iff.intro h1 h2``从``h1 : p → q``和``h2 : q → p``生成了``p ↔ q``的证明。表达式``Iff.mp h``从``h : p ↔ q``生成了``p → q``的证明。表达式``Iff.mpr h``从``h : p ↔ q``生成了``q → p``的证明。下面是``p ∧ q ↔ q ∧ p``的证明：

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h
```

我们可以用匿名构造子表示法来，从正反两个方向的证明，来构建``p ↔ q``的证明。我们也可以使用``.``符号连接``mp``和``mpr``。因此，前面的例子可以简写如下：

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
```

## 引入辅助子目标

这里介绍Lean提供的另一种帮助构造长证明的方法，即``have``结构，它在证明中引入了一个辅助的子目标。下面是一个小例子，改编自上一节:

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
```

在内部，表达式``have h : p := s; t``产生项``(fun (h : p) => t) s``。换句话说，``s``是``p``的证明，``t``是假设``h : p``的期望结论的证明，并且这两个是由lambda抽象和应用组合在一起的。这个简单的方法在构建长证明时非常有用，因为我们可以使用中间的``have``作为通向最终目标的垫脚石。

Lean还支持从目标向后推理的结构化方法，它模仿了普通数学文献中“足以说明某某”（suffices to show）的构造。下一个例子简单地排列了前面证明中的最后两行。

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h
```

``suffices hq : q``给出了两条目标。第一，我们需要证明，通过利用附加假设``hq : q``证明原目标``q ∧ p``，这样足以证明``q``，第二，我们需要证明``q``。

## 经典逻辑

到目前为止，我们看到的引入和消去规则都是构造主义的，也就是说，它们反映了基于命题即类型对应的逻辑连接词的计算理解。普通经典逻辑在此基础上加上了排中律``p ∨ ¬p``（excluded middle, em）。要使用这个原则，你必须打开经典逻辑命名空间。

```lean
open Classical

variable (p : Prop)
#check em p
```

从直觉上看，构造主义的“或”非常强：断言``p ∨ q``等于知道哪个是真实情况。如果``RH``代表黎曼猜想，经典数学家愿意断言``RH ∨ ¬RH``，即使我们还不能断言析取式的任何一端。

排中律的一个结果是双重否定消去规则（double-negation elimination, dne）:

```lean
open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
```

双重否定消去规则给出了一种证明任何命题``p``的方法：通过假设``¬p``来推导出``false``，相当于证明了``p``。换句话说，双重否定消除允许反证法，这在构造主义逻辑中通常是不可能的。作为练习，你可以试着证明相反的情况，也就是说，证明``em``可以由``dne``证明。

经典公理还可以通过使用``em``让你获得额外的证明模式。例如，我们可以通过案例进行证明:

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)
```

或者你可以用反证法来证明：

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)
```

如果你不习惯构造主义，你可能需要一些时间来了解经典推理在哪里使用。在下面的例子中，它是必要的，因为从一个构造主义的观点来看，知道``p``和``q``不同时真并不一定告诉你哪一个是假的：

```lean
open Classical
variable (p q : Prop)

-- BEGIN
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)
```

稍后我们将看到，构造逻辑中*有*某些情况允许“排中律”和“双重否定消除律”等，而Lean支持在这种情况下使用经典推理，而不依赖于排中律。

Lean中使用的公理的完整列表见[公理与计算](./axioms_and_computation.md)。

## 逻辑命题的例子
------------------------------------

Lean的标准库包含了许多命题逻辑的有效语句的证明，你可以自由地在自己的证明中使用这些证明。下面的列表包括一些常见的逻辑等价式。

交换律：

1. ``p ∧ q ↔ q ∧ p``
2. ``p ∨ q ↔ q ∨ p``

结合律：

3. ``(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)``
4. ``(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)``

分配律：

5. ``p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)``
6. ``p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)``

其他性质：

1. ``(p → (q → r)) ↔ (p ∧ q → r)``
2. ``((p ∨ q) → r) ↔ (p → r) ∧ (q → r)``
3. ``¬(p ∨ q) ↔ ¬p ∧ ¬q``
4.  ``¬p ∨ ¬q → ¬(p ∧ q)``
11. ``¬(p ∧ ¬p)``
12. ``p ∧ ¬q → ¬(p → q)``
13. ``¬p → (p → q)``
14. ``(¬p ∨ q) → (p → q)``
15. ``p ∨ False ↔ p``
16. ``p ∧ False ↔ False``
17. ``¬(p ↔ ¬p)``
18. ``(p → q) → (¬q → ¬p)``

经典推理：

19. ``(p → r ∨ s) → ((p → r) ∨ (p → s))``
20. ``¬(p ∧ q) → ¬p ∨ ¬q``
21. ``¬(p → q) → p ∧ ¬q``
22. ``(p → q) → (¬p ∨ q)``
23. ``(¬q → ¬p) → (p → q)``
24. ``p ∨ ¬p``
25. ``(((p → q) → p) → p)``

``sorry``标识符神奇地生成任何东西的证明，或者提供任何数据类型的对象。当然，作为一种证明方法，它是不可靠的——例如，你可以使用它来证明``False``——并且当文件使用或导入依赖于它的定理时，Lean会产生严重的警告。但它对于增量地构建长证明非常有用。从上到下写证明，用``sorry``来填子证明。确保Lean接受所有的``sorry``；如果不是，则有一些错误需要纠正。然后返回，用实际的证据替换每个``sorry``，直到做完。

有另一个有用的技巧。你可以使用下划线``_``作为占位符，而不是``sorry``。回想一下，这告诉Lean该参数是隐式的，应该自动填充。如果Lean尝试这样做并失败了，它将返回一条错误消息“不知道如何合成占位符”（Don't know how to synthesize placeholder），然后是它所期望的项的类型，以及上下文中可用的所有对象和假设。换句话说，对于每个未解决的占位符，Lean报告在那一点上需要填充的子目标。然后，你可以通过递增填充这些占位符来构造一个证明。

这里有两个简单的证明例子作为参考。

```lean
open Classical

-- 分配律
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- 需要一点经典推理的例子
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
```

## 练习

证明以下等式，用真实证明取代“sorry”占位符。

```lean
variable (p q r : Prop)

--  ∧ 和 ∨ 的交换律
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- ∧ 和 ∨ 的结合律
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- 分配律
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- 其他性质
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
```

证明以下等式，用真实证明取代“sorry”占位符。这里需要一点经典逻辑。

```lean
open Classical

variable (p q r s : Prop)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
```

证明``¬(p ↔ ¬p)``且不使用经典逻辑。