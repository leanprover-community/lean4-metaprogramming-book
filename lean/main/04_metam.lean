/-
# `MetaM`

The Lean 4 metaprogramming API is organised around a small zoo of monads. The
four main ones are:

Lean 4 のメタプログラミングAPIは、小さなモナドの集まりを中心に構成されています。主な4つは次のとおりです:

- `CoreM` gives access to the *environment*, i.e. the set of things that
  have been declared or imported at the current point in the program.
- `MetaM` gives access to the *metavariable context*, i.e. the set of
  metavariables that are currently declared and the values assigned to them (if
  any).
- `TermElabM` gives access to various information used during elaboration.
- `TacticM` gives access to the list of current goals.

- `CoreM`は、プログラムの現在地点で宣言されたりインポートされたりしたものの集合、
  すなわち*環境*へのアクセスを提供します。
- `MetaM`は、現在宣言されているメタ変数の集合とそれらに割り当てられた値（あれば）を含む
  *メタ変数の文脈*へのアクセスを提供します。
- `TermElabM`は、展開（elaboration）中に使用されるさまざまな情報へのアクセスを提供します。
- `TacticM`は、現在のゴールのリストへのアクセスを提供します。

These monads extend each other, so a `MetaM` operation also has access to the
environment and a `TermElabM` computation can use metavariables. There are also
other monads which do not neatly fit into this hierarchy, e.g. `CommandElabM`
extends `MetaM` but neither extends nor is extended by `TermElabM`.

これらのモナドは互いに拡張されているため、`MetaM`の操作は環境にもアクセスでき、
`TermElabM`の計算はメタ変数を使用できます。この階層にきれいには収まらない他のモナドもあります。
たとえば、`CommandElabM`は`MetaM`を拡張していますが、`TermElabM`を拡張したり拡張されたりしていません。

This chapter demonstrates a number of useful operations in the `MetaM` monad.
`MetaM` is of particular importance because it allows us to give meaning to
every expression: the environment (from `CoreM`) gives meaning to constants like
`Nat.zero` or `List.map` and the metavariable context gives meaning to both
metavariables and local hypotheses. 

この章では、`MetaM`モナドでのいくつかの有用な操作を紹介します。
`MetaM`は特に重要で、すべての式に意味を付けることを可能にします。
環境（`CoreM`から）は、`Nat.zero`や`List.map`のような定数に意味を与え、
メタ変数の文脈はメタ変数とローカル仮説の両方に意味を与えます。

-/

import Lean

open Lean Lean.Expr Lean.Meta

/-!
## Metavariables

### Overview

The 'Meta' in `MetaM` refers to metavariables, so we should talk about these
first. Lean users do not usually interact much with metavariables -- at least
not consciously -- but they are used all over the place in metaprograms. There
are two ways to view them: as holes in an expression or as goals.

`MetaM`の「Meta」はメタ変数を指しているので、まずこれについて話しましょう。
Leanのユーザーは、メタ変数と意識的にはあまりやり取りしませんが、
メタプログラムのあちこちで使用されています。
メタ変数を見る方法は2つあります。式の穴として、またはゴールとしてです。

Take the goal perspective first. When we prove things in Lean, we always operate
on goals, such as

まずゴールの観点から見てみましょう。
Leanで証明するときは、常にゴールを操作します。

```lean
n m : Nat
⊢ n + m = m + n
```

These goals are internally represented by metavariables. Accordingly, each
metavariable has a *local context* containing hypotheses 
(here `[n : Nat, m :Nat]`) and a *target type* (here `n + m = m + n`). Metavariables also have a
unique name, say `m`, and we usually render them as `?m`.

これらのゴールは、内部的にはメタ変数で表されます。
したがって、各メタ変数には、仮説（ここでは`[n : Nat, m : Nat]`）を含む*ローカルコンテキスト*と、
*ターゲット型*（ここでは`n + m = m + n`）があります。
メタ変数にはユニークな名前、たとえば`m`があり、通常は`?m`としてレンダリングされます。

To close a goal, we must give an expression `e` of the target type. The
expression may contain fvars from the metavariable's local context, but no
others. Internally, closing a goal in this way corresponds to *assigning* the
metavariable; we write `?m := e` for this assignment.

ゴールを閉じるには、ターゲット型の式`e`を与える必要があります。
式には、メタ変数のローカルコンテキストのfvarを含めることができますが、
他のものは含めることができません。
内部的には、このようにゴールを閉じることは、メタ変数を*割り当てる*ことに対応します。
この割り当てには`?m := e`と書きます。

The second, complementary view of metavariables is that they represent holes
in an expression. For instance, an application of `Eq.trans` may generate two
goals which look like this:

メタ変数の2番目の補完的な見方は、式の穴を表すということです。
例えば、`Eq.trans`の適用により、次のような2つのゴールが生成されることがあります:

```lean
n m : Nat
⊢ n = ?x

n m : Nat
⊢ ?x = m
```

Here `?x` is another metavariable -- a hole in the target types of both goals,
to be filled in later during the proof. The type of `?x` is `Nat` and its local
context is `[n : Nat, m : Nat]`. Now, if we solve the first goal by reflexivity,
then `?x` must be `n`, so we assign `?x := n`. Crucially, this also affects the
second goal: it is "updated" (not really, as we will see) to have target `n =
m`. The metavariable `?x` represents the same expression everywhere it occurs.

ここで、`?x`は別のメタ変数です。これは、後で証明中に埋めるための、両方のゴールのターゲット型の穴です。
`?x`の型は`Nat`で、ローカルコンテキストは`[n : Nat, m : Nat]`です。
さて、最初のゴールを反射性で解決すると、`?x`は`n`でなければならないので、`?x := n`とします。
重要なことに、これは2番目のゴールにも影響します。
（実際にはそうではありませんが、後で見るように）`n = m`というターゲットを持つように「更新」されます。
メタ変数`?x`は、出現する場所に関係なく、同じ式を表します。

### Tactic Communication via Metavariables

Tactics use metavariables to communicate the current goals. To see how, consider
this simple (and slightly artificial) proof:

タクティックは、現在のゴールを伝えるためにメタ変数を使用します。
これがどのように機能するかを確認するには、次の単純な（そして少し人工的な）証明を考えてみましょう。
-/

example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans 
  apply h
  apply h a

/-!
After we enter tactic mode, our ultimate goal is to generate an expression of
type `f (f a) = a` which may involve the hypotheses `α`, `a`, `f` and `h`. So
Lean generates a metavariable `?m1` with target `f (f a) = a` and a local
context containing these hypotheses. This metavariable is passed to the first
`apply` tactic as the current goal.

タクティックモードに入った後、最終的な目標は、仮説`α`、`a`、`f`、そして`h`を用いて、
タイプ`f (f a) = a`の式を生成することです。
したがって、Leanは、ターゲットが`f (f a) = a`で、
これらの仮説を含むローカルコンテキストを持つメタ変数`?m1`を生成します。
このメタ変数は、最初の`apply`タクティックに現在のゴールとして渡されます。

The `apply` tactic then tries to apply `Eq.trans` and succeeds, generating three
new metavariables:

`apply`タクティックは、`Eq.trans`を適用しようとします。

```lean
...
⊢ f (f a) = ?b

...
⊢ ?b = a

...
⊢ α
```

Call these metavariables `?m2`, `?m3` and `?b`. The last one, `?b`, stands for
the intermediate element of the transitivity proof and occurs in `?m2` and
`?m3`. The local contexts of all metavariables in this proof are the same, so
we omit them.

このとき、`?m2`、`?m3`、`?b`という新しいメタ変数が生成されます。
最後の`?b`は、推移性の証明の中間要素を表し、`?m2`と`?m3`に出現します。
この証明のすべてのメタ変数のローカルコンテキストは同じなので、省略します。

Having created these metavariables, `apply` assigns

これらのメタ変数を作成した後、`apply`は次のように割り当てます。

```lean
?m1 := @Eq.trans α (f (f a)) ?b a ?m2 ?m3
```

and reports that `?m2`, `?m3` and `?b` are now the current goals.

そして、`?m2`、`?m3`、`?b`が現在のゴールであると報告します。

At this point the second `apply` tactic takes over. It receives `?m2` as the
current goal and applies `h` to it. This succeeds and the tactic assigns 
`?m2 := h (f a)`. This assignment implies that `?b` must be `f a`, so the tactic also
assigns `?b := f a`. Assigned metavariables are not considered open goals, so
the only goal that remains is `?m3`.

ここで、2番目の`apply`タクティックが引き継ぎます。
これは、現在のゴールとして`?m2`を受け取り、`h`を適用します。
これは成功し、タクティックは`?m2 := h (f a)`と割り当てます。
この割り当ては、`?b`が`f a`でなければならないことを意味するため、
タクティックは`?b := f a`と割り当てます。
割り当てられたメタ変数はオープンゴールとは見なされないため、
残っているのは`?m3`だけです。

Now the third `apply` comes in. Since `?b` has been assigned, the target of
`?m3` is now `f (f a) = a`. Again, the application of `h` succeeds and the
tactic assigns `?m3 := h a`.
----------?m3は f a = aなのでは？----------

次に、3番目の`apply`が入ります。
`?b`が割り当てられているため、`?m3`のターゲットは`f (f a) = a`になります。
再び、`h`の適用が成功し、タクティックは`?m3 := h a`と割り当てます。

At this point, all metavariables are assigned as follows:

この時点で、すべてのメタ変数は次のように割り当てられます。

```lean
?m1 := @Eq.trans α (f (f a)) ?b a ?m2 ?m3
?m2 := h (f a)
?m3 := h a
?b  := f a
```

Exiting the `by` block, Lean constructs the final proof term by taking the
assignment of `?m1` and replacing each metavariable with its assignment. This
yields

`by`ブロックを抜けると、Leanは`?m1`の割り当てを取り出し、
各メタ変数をその割り当てで置き換えて最終的な証明項を構築します。
これにより、次のようになります。

```lean
@Eq.trans α (f (f a)) (f a) a (h (f a)) (h a)
```

The example also shows how the two views of metavariables -- as holes in an
expression or as goals -- are related: the goals we get are holes in the final
proof term.

この例は、メタ変数の2つの見方（式の穴として、またはゴールとして）がどのように関連しているかも示しています。
得られるゴールは、最終的な証明項の穴です。


### Basic Operations

Let us make these concepts concrete. When we operate in the `MetaM` monad, we
have read-write access to a `MetavarContext` structure containing information
about the currently declared metavariables. Each metavariable is identified by
an `MVarId` (a unique `Name`). To create a new metavariable, we use
`Lean.Meta.mkFreshExprMVar` with type

これらの概念を具体的にしましょう。
`MetaM`モナドで操作するとき、現在宣言されているメタ変数に関する情報を含む
`MetavarContext`構造への読み書きアクセスがあります。
各メタ変数は`MVarId`（一意の`Name`）で識別されます。
新しいメタ変数を作成するには、型`Lean.Meta.mkFreshExprMVar`を使用します。

```lean
mkFreshExprMVar (type? : Option Expr) (kind := MetavarKind.natural)
    (userName := Name.anonymous) : MetaM Expr
```

Its arguments are:

- `type?`: the target type of the new metavariable. If `none`, the target type
  is `Sort ?u`, where `?u` is a universe level metavariable. (This is a special
  class of metavariables for universe levels, distinct from the expression
  metavariables which we have been calling simply "metavariables".)

- `type?`: 新しいメタ変数のターゲットタイプです。
  `none`の場合、ターゲットタイプは `Sort ?u`で、ここで `?u` は宇宙レベルのメタ変数です。 
  (これは、単に「メタ変数」と呼んでいる表現メタ変数とは異なる、
  宇宙レベルのための特別なクラスのメタ変数です。)

- `kind`: the metavariable kind. See the [Metavariable Kinds
  section](#metavariable-kinds) (but the default is usually correct).

- `kind`: メタ変数の種類です。
  [Metavariable Kinds section](#metavariable-kinds)を参照してください
  （ただし、デフォルトは通常正しいです）。

- `userName`: the new metavariable's user-facing name. This is what gets printed
  when the metavariable appears in a goal. Unlike the `MVarId`, this name does
  not need to be unique.

- `userName`: 新しいメタ変数のユーザー向け名前です。
  これは、メタ変数がゴールに表示されるときに印刷されます。
  `MVarId`とは異なり、この名前は一意である必要はありません。

The returned `Expr` is always a metavariable. We can use `Lean.Expr.mvarId!` to
extract the `MVarId`, which is guaranteed to be unique. (Arguably
`mkFreshExprMVar` should just return the `MVarId`.)

返される`Expr`は常にメタ変数です。
`Lean.Expr.mvarId!`を使用して`MVarId`を取り出すことができます。
これは一意であることが保証されています。
（おそらく`mkFreshExprMVar`は単に`MVarId`を返すべきです。）

The local context of the new metavariable is inherited from the current local
context, more about which in the next section. If you want to give a different
local context, use `Lean.Meta.mkFreshExprMVarAt`.

新しいメタ変数のローカルコンテキストは、現在のローカルコンテキストから継承されます。
次のセクションで詳しく説明します。
別のローカルコンテキストを与えたい場合は、`Lean.Meta.mkFreshExprMVarAt`を使用します。

Metavariables are initially unassigned. To assign them, use
`Lean.MVarId.assign` with type

メタ変数は最初は割り当てられていません。
それらを割り当てるには、型がある`Lean.MVarId.assign`を使用します。

```lean
assign (mvarId : MVarId) (val : Expr) : MetaM Unit
```

This updates the `MetavarContext` with the assignment `?mvarId := val`. You must
make sure that `mvarId` is not assigned yet (or that the old assignment is
definitionally equal to the new assignment). You must also make sure that the
assigned value, `val`, has the right type. This means (a) that `val` must have
the target type of `mvarId` and (b) that `val` must only contain fvars from the
local context of `mvarId`.

これにより、`MetavarContext`が割り当て`?mvarId := val`で更新されます。
`mvarId`がまだ割り当てられていないこと（または古い割り当てが新しい割り当てと定義的に等しいこと）
を確認する必要があります。
また、割り当てられた値`val`が正しい型であることも確認する必要があります。
これは、(a)`val`が`mvarId`のターゲットタイプを持っている必要があること、
(b)`val`が`mvarId`のローカルコンテキストのfvarのみを含んでいる必要があることを意味します。

If you `#check Lean.MVarId.assign`, you will see that its real type is more
general than the one we showed above: it works in any monad that has access to a
`MetavarContext`. But `MetaM` is by far the most important such monad, so in
this chapter, we specialise the types of `assign` and similar functions.

`#check Lean.MVarId.assign`を実行すると、
その実際の型が上記に示したものよりも一般的であることがわかります。
これは、`MetavarContext`にアクセスできる任意のモナドで動作します。
しかし、`MetaM`はこれらのモナドの中で最も重要なものです。
そのため、この章では、`assign`や類似の関数の型を特殊化します。

To get information about a declared metavariable, use `Lean.MVarId.getDecl`.
Given an `MVarId`, this returns a `MetavarDecl` structure. (If no metavariable
with the given `MVarId` is declared, the function throws an exception.) The
`MetavarDecl` contains information about the metavariable, e.g. its type, local
context and user-facing name. This function has some convenient variants, such
as `Lean.MVarId.getType`.

宣言されたメタ変数に関する情報を取得するには、`Lean.MVarId.getDecl`を使用します。
`MVarId`が与えられると、`MetavarDecl`構造体が返されます。
（指定された`MVarId`のメタ変数が宣言されていない場合、関数は例外をスローします。）
`MetavarDecl`には、メタ変数に関する情報が含まれています。
例えば、その型、ローカルコンテキスト、ユーザー向けの名前などです。
この関数には、`Lean.MVarId.getType`などの便利なバリアントがあります。

To get the current assignment of a metavariable (if any), use
`Lean.getExprMVarAssignment?`. To check whether a metavariable is assigned, use
`Lean.MVarId.isAssigned`. However, these functions are relatively rarely
used in tactic code because we usually prefer a more powerful operation:
`Lean.Meta.instantiateMVars` with type

メタ変数の現在の割り当て（あれば）を取得するには、`Lean.getExprMVarAssignment?`を使用します。
メタ変数が割り当てられているかどうかを確認するには、`Lean.MVarId.isAssigned`を使用します。
しかし、これらの関数は、あまり使われません。なぜなら、通常はより強力な操作を好むからです。
型が`Lean.Meta.instantiateMVars`である場合

```lean
instantiateMVars : Expr → MetaM Expr
```

Given an expression `e`, `instantiateMVars` replaces any assigned metavariable
`?m` in `e` with its assigned value. Unassigned metavariables remain as they
are.

式`e`が与えられた場合、`instantiateMVars`は、式`e`内の割り当てられたメタ変数`?m`を、
その割り当てられた値に置き換えます。
割り当てられていないメタ変数はそのままです。

This operation should be used liberally. When we assign a metavariable, existing
expressions containing this metavariable are not immediately updated. This is a
problem when, for example, we match on an expression to check whether it is an
equation. Without `instantiateMVars`, we might miss the fact that the expression
`?m`, where `?m` happens to be assigned to `0 = n`, represents an equation. In
other words, `instantiateMVars` brings our expressions up to date with the
current metavariable state.

この操作は自由に使用する必要があります。
メタ変数を割り当てると、このメタ変数を含む既存の式はすぐには更新されません。
たとえば、式をマッチングして、それが方程式であるかどうかを確認する場合、このことは問題です。
`instantiateMVars`がないと、`?m`という式が方程式を表していることを見逃す可能性があります。
ここで、`?m`は`0 = n`に割り当てられているとします。
言い換えると、`instantiateMVars`は、式を現在のメタ変数の状態に合わせて最新の状態にします。

Instantiating metavariables requires a full traversal of the input expression,
so it can be somewhat expensive. But if the input expression does not contain
any metavariables, `instantiateMVars` is essentially free. Since this is the
common case, liberal use of `instantiateMVars` is fine in most situations.

メタ変数をインスタンス化するには、入力式の完全なトラバースが必要なため、
多少高価になる可能性があります。
しかし、入力式にメタ変数が含まれていない場合、`instantiateMVars`は本質的に無料です。
これが一般的なケースなので、`instantiateMVars`の自由な使用は、ほとんどの状況では問題ありません。

Before we go on, here is a synthetic example demonstrating how the basic
metavariable operations are used. More natural examples appear in the following
sections.

次に、基本的なメタ変数操作がどのように使用されるかを示す合成例を示します。
より自然な例は、次のセクションで説明します。
-/

#eval show MetaM Unit from do
  -- Create two fresh metavariables of type `Nat`.
  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
  let mvar2 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar2)
  -- Create a fresh metavariable of type `Nat → Nat`. The `mkArrow` function
  -- creates a function type.
  let mvar3 ← mkFreshExprMVar (← mkArrow (.const ``Nat []) (.const ``Nat []))
    (userName := `mvar3)

  -- Define a helper function that prints each metavariable.
  let printMVars : MetaM Unit := do
    IO.println s!"  meta1: {← instantiateMVars mvar1}"
    IO.println s!"  meta2: {← instantiateMVars mvar2}"
    IO.println s!"  meta3: {← instantiateMVars mvar3}"

  IO.println "Initially, all metavariables are unassigned:"
  printMVars

  -- Assign `mvar1 : Nat := ?mvar3 ?mvar2`.
  mvar1.mvarId!.assign (.app mvar3 mvar2)
  IO.println "After assigning mvar1:"
  printMVars

  -- Assign `mvar2 : Nat := 0`.
  mvar2.mvarId!.assign (.const ``Nat.zero [])
  IO.println "After assigning mvar2:"
  printMVars

  -- Assign `mvar3 : Nat → Nat := Nat.succ`.
  mvar3.mvarId!.assign (.const ``Nat.succ [])
  IO.println "After assigning mvar3:"
  printMVars
-- Initially, all metavariables are unassigned:
--   meta1: ?_uniq.1
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- After assigning mvar1:
--   meta1: ?_uniq.3 ?_uniq.2
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- After assigning mvar2:
--   meta1: ?_uniq.3 Nat.zero
--   meta2: Nat.zero
--   meta3: ?_uniq.3
-- After assigning mvar3:
--   meta1: Nat.succ Nat.zero
--   meta2: Nat.zero
--   meta3: Nat.succ


/-!
### Local Contexts

Consider the expression `e` which refers to the free variable with unique name
`h`:

`h`というユニークな名前の自由変数を参照する式`e`を考えてみてください:

```lean
e := .fvar (FVarId.mk `h)
```

What is the type of this expression? The answer depends on the local context in
which `e` is interpreted. One local context may declare that `h` is a local
hypothesis of type `Nat`; another local context may declare that `h` is a local
definition with value `List.map`.

この式の型は何ですか？答えは、`e`が解釈されるローカルコンテキストに依存します。
1つのローカルコンテキストは、`h`が`Nat`型のローカル仮説であることを宣言するかもしれません。
別のローカルコンテキストは、`h`が値`List.map`のローカル定義であることを宣言するかもしれません。

Thus, expressions are only meaningful if they are interpreted in the local
context for which they were intended. And as we saw, each metavariable has its
own local context. So in principle, functions which manipulate expressions
should have an additional `MVarId` argument specifying the goal in which the
expression should be interpreted.

したがって、式は、意図されたローカルコンテキストで解釈された場合にのみ意味があります。
そして、見たように、各メタ変数には独自のローカルコンテキストがあります。
したがって、式を操作する関数は、式を解釈するべきゴールを指定する追加の`MVarId`引数を持つべきです。

That would be cumbersome, so Lean goes a slightly different route. In `MetaM`,
we always have access to an ambient `LocalContext`, obtained with `Lean.getLCtx`
of type

それは面倒ですので、Leanは少し異なるルートをたどります。
`MetaM`では、常に`Lean.getLCtx`の型で取得される環境`LocalContext`にアクセスできます。

```lean
getLCtx : MetaM LocalContext
```

All operations involving fvars use this ambient local context.

fvarを含むすべての操作は、この環境ローカルコンテキストを使用します。

The downside of this setup is that we always need to update the ambient local
context to match the goal we are currently working on. To do this, we use
`Lean.MVarId.withContext` of type

この設定の欠点は、常に現在作業しているゴールに一致するように環境ローカルコンテキストを更新する必要があることです。
これを行うには、型の`Lean.MVarId.withContext`を使用します。

```lean
withContext (mvarId : MVarId) (c : MetaM α) : MetaM α
```

This function takes a metavariable `mvarId` and a `MetaM` computation `c` and
executes `c` with the ambient context set to the local context of `mvarId`. A
typical use case looks like this:

この関数は、メタ変数`mvarId`と`MetaM`計算`c`を取り、`c`を実行し、
環境コンテキストを`mvarId`のローカルコンテキストに設定します。
典型的な使用例は次のようになります。

```lean
def someTactic (mvarId : MVarId) ... : ... :=
  mvarId.withContext do
    ...
```

The tactic receives the current goal as the metavariable `mvarId` and
immediately sets the current local context. Any operations within the `do` block
then use the local context of `mvarId`.

タクティックは、現在のゴールをメタ変数`mvarId`として受け取り、すぐに現在のローカルコンテキストを設定します。
`do`ブロック内のすべての操作は、`mvarId`のローカルコンテキストを使用します。

Once we have the local context properly set, we can manipulate fvars. Like
metavariables, fvars are identified by an `FVarId` (a unique `Name`). Basic
operations include:

ローカルコンテキストが適切に設定されると、fvarを操作できます。
メタ変数と同様に、fvarは`FVarId`（ユニークな`Name`）で識別されます。

- `Lean.FVarId.getDecl : FVarId → MetaM LocalDecl` retrieves the declaration
  of a local hypothesis. As with metavariables, a `LocalDecl` contains all
  information pertaining to the local hypothesis, e.g. its type and its
  user-facing name.
  
- `Lean.Meta.getLocalDeclFromUserName : Name → MetaM LocalDecl` retrieves the
  declaration of the local hypothesis with the given user-facing name. If there
  are multiple such hypotheses, the bottommost one is returned. If there is
  none, an exception is thrown.

- `Lean.FVarId.getDecl : FVarId → MetaM LocalDecl` はローカル仮説の宣言を取得します。
  メタ変数と同様に、`LocalDecl`には、ローカル仮説に関するすべての情報が含まれています。
  例えば、その型とユーザー向けの名前です。

- `Lean.Meta.getLocalDeclFromUserName : Name → MetaM LocalDecl` は、
  指定されたユーザー向けの名前を持つローカル仮説の宣言を取得します。
  そのような仮説が複数ある場合は、最下部の仮説が返されます。
  ない場合は、例外がスローされます。

We can also iterate over all hypotheses in the local context, using the `ForIn`
instance of `LocalContext`. A typical pattern is this:

また、`LocalContext`の`ForIn`インスタンスを使用して、
ローカルコンテキストのすべての仮説を反復処理することもできます。
典型的なパターンは次のとおりです。

```lean
for ldecl in ← getLCtx do
  if ldecl.isImplementationDetail then
    continue
  -- do something with the ldecl
```

The loop iterates over every `LocalDecl` in the context. The
`isImplementationDetail` check skips local hypotheses which are 'implementation
details', meaning they are introduced by Lean or by tactics for bookkeeping
purposes. They are not shown to users and tactics are expected to ignore them.

ループは、コンテキスト内のすべての`LocalDecl`を反復処理します。
`isImplementationDetail`チェックは、ローカル仮説をスキップします。
これらは「実装の詳細」と呼ばれ、Leanまたはタクティックによって導入されます。
これらはユーザーに表示されず、タクティックはこれらを無視することが期待されます。

At this point, we can build the `MetaM` part of an `assumption` tactic:

この時点で、`assumption`タクティックの`MetaM`部分を構築できます。
-/

def myAssumption (mvarId : MVarId) : MetaM Bool := do
  -- Check that `mvarId` is not already assigned.
  mvarId.checkNotAssigned `myAssumption
  -- Use the local context of `mvarId`.
  mvarId.withContext do
    -- The target is the type of `mvarId`.
    let target ← mvarId.getType
    -- For each hypothesis in the local context:
    for ldecl in ← getLCtx do
      -- If the hypothesis is an implementation detail, skip it.
      if ldecl.isImplementationDetail then
        continue
      -- If the type of the hypothesis is definitionally equal to the target
      -- type:
      if ← isDefEq ldecl.type target then
        -- Use the local hypothesis to prove the goal.
        mvarId.assign ldecl.toExpr
        -- Stop and return true.
        return true
    -- If we have not found any suitable local hypothesis, return false.
    return false

/-
The `myAssumption` tactic contains three functions we have not seen before:

`myAssumption`タクティックには、これまで見たことのない3つの関数が含まれています。

- `Lean.MVarId.checkNotAssigned` checks that a metavariable is not already
  assigned. The 'myAssumption' argument is the name of the current tactic. It is
  used to generate a nicer error message.
- `Lean.Meta.isDefEq` checks whether two definitions are definitionally equal.
  See the [Definitional Equality section](#definitional-equality).
- `Lean.LocalDecl.toExpr` is a helper function which constructs the `fvar`
  expression corresponding to a local hypothesis.

- `Lean.MVarId.checkNotAssigned`は、メタ変数がすでに割り当てられていないことを確認します。
  「myAssumption」引数は、現在のタクティックの名前です。
  より良いエラーメッセージを生成するために使用されます。
- `Lean.Meta.isDefEq`は、2つの定義が定義的に等しいかどうかを確認します。
  [Definitional Equality section](#definitional-equality)を参照してください。
- `Lean.LocalDecl.toExpr`は、ローカル仮説に対応する`fvar`式を構築するヘルパー関数です。


### Delayed Assignments

The above discussion of metavariable assignment contains a lie by omission:
there are actually two ways to assign a metavariable. We have seen the regular
way; the other way is called a *delayed assignment*.

メタ変数の割り当てに関する上記の議論には、欠落による嘘が含まれています。
実際には、メタ変数を割り当てる方法は2つあります。
通常の方法を見ました。もう一つは*遅延割り当て*と呼ばれます。

We do not discuss delayed assignments in any detail here since they are rarely
useful for tactic writing. If you want to learn more about them, see the
comments in `MetavarContext.lean` in the Lean standard library. But they create
two complications which you should be aware of.

ここでは、遅延割り当てについては詳しく説明しません。
タクティックの記述にはあまり役に立たないためです。
それらについてもっと学びたい場合は、
Lean標準ライブラリの`MetavarContext.lean`のコメントを参照してください。
しかし、それらは2つの複雑さを作成します。
それらについて知っておく必要があります。

First, delayed assignments make `Lean.MVarId.isAssigned` and
`getExprMVarAssignment?` medium-calibre footguns. These functions only check for
regular assignments, so you may need to use `Lean.MVarId.isDelayedAssigned`
and `Lean.Meta.getDelayedMVarAssignment?` as well.

最初に、遅延割り当ては、`Lean.MVarId.isAssigned`と`getExprMVarAssignment?`を
中間キャリバーのフットガンにします。
これらの関数は通常の割り当てのみをチェックするため、
`Lean.MVarId.isDelayedAssigned`と`Lean.Meta.getDelayedMVarAssignment?`も使用する必要があります。

Second, delayed assignments break an intuitive invariant. You may have assumed
that any metavariable which remains in the output of `instantiateMVars` is
unassigned, since the assigned metavariables have been substituted. But delayed
metavariables can only be substituted once their assigned value contains no
unassigned metavariables. So delayed-assigned metavariables can appear in an
expression even after `instantiateMVars`.

2番目に、遅延割り当ては直感的な不変条件を破ります。
`instantiateMVars`の出力に残っているメタ変数は、割り当てられていないと仮定しているかもしれません。
割り当てられたメタ変数は置換されているためです。
しかし、遅延メタ変数は、割り当てられた値に未割り当てのメタ変数が含まれていない場合にのみ置換できます。
したがって、遅延割り当てされたメタ変数は、`instantiateMVars`の後でも式に現れることがあります。


### Metavariable Depth

Metavariable depth is also a niche feature, but one that is occasionally useful.
Any metavariable has a *depth* (a natural number), and a `MetavarContext` has a
corresponding depth as well. Lean only assigns a metavariable if its depth is
equal to the depth of the current `MetavarContext`. Newly created metavariables
inherit the `MetavarContext`'s depth, so by default every metavariable is
assignable.

メタ変数の深さもニッチな機能ですが、時には役に立ちます。
メタ変数には*深さ*（自然数）があり、`MetavarContext`にも対応する深さがあります。
Leanは、メタ変数の深さが現在の`MetavarContext`の深さと等しい場合にのみ、メタ変数を割り当てます。
新しく作成されたメタ変数は、`MetavarContext`の深さを継承します。
したがって、デフォルトではすべてのメタ変数が割り当て可能です。

This setup can be used when a tactic needs some temporary metavariables and also
needs to make sure that other, non-temporary metavariables will not be assigned.
To ensure this, the tactic proceeds as follows:

このセットアップは、タクティックが一時的なメタ変数と、
他の一時的でないメタ変数が割り当てられないようにする必要がある場合に使用できます。
これを確実にするために、タクティックは次のように進みます。

1. Save the current `MetavarContext`.
2. Increase the depth of the `MetavarContext`.
3. Perform whatever computation is necessary, possibly creating and assigning
   metavariables. Newly created metavariables are at the current depth of the
   `MetavarContext` and so can be assigned. Old metavariables are at a lower
   depth, so cannot be assigned.
4. Restore the saved `MetavarContext`, thereby erasing all the temporary
   metavariables and resetting the `MetavarContext` depth.

1. 現在の`MetavarContext`を保存します。
2. `MetavarContext`の深さを増やします。
3. 必要な計算を実行し、メタ変数を作成して割り当てることができます。
   新しく作成されたメタ変数は、現在の`MetavarContext`の深さにあります。
   したがって、割り当てることができます。
   古いメタ変数は、より低い深さにあり、割り当てることはできません。
4. 保存された`MetavarContext`を復元し、一時的なメタ変数をすべて消去し、
    `MetavarContext`の深さをリセットします。

This pattern is encapsulated in `Lean.Meta.withNewMCtxDepth`.

このパターンは、`Lean.Meta.withNewMCtxDepth`にカプセル化されています。


## Computation

Computation is a core concept of dependent type theory. The terms `2`, `Nat.succ
1` and `1 + 1` are all "the same" in the sense that they compute the same value.
We call them *definitionally equal*. The problem with this, from a
metaprogramming perspective, is that definitionally equal terms may be
represented by entirely different expressions, but our users would usually
expect that a tactic which works for `2` also works for `1 + 1`. So when we
write our tactics, we must do additional work to ensure that definitionally
equal terms are treated similarly.

計算は、依存型理論の核心的な概念です。
項`2`、`Nat.succ 1`、`1 + 1`は、すべて同じ意味で「同じ」です。
つまり、同じ値を計算します。これらを*定義的に等しい*と呼びます。
メタプログラミングの観点からは、これには問題があります。
定義的に等しい項は、まったく異なる式で表される可能性がありますが、
ユーザーは通常、`2`にも`1 + 1`にも機能するタクティックを期待しています。
したがって、タクティックを書くときは、定義的に等しい項が同様に扱われるようにするための追加の作業が必要です。

### Full Normalisation

The simplest thing we can do with computation is to bring a term into normal
form. With some exceptions for numeric types, the normal form of a term `t` of
type `T` is a sequence of applications of `T`'s constructors. E.g. the normal
form of a list is a sequence of applications of `List.cons` and `List.nil`.

計算でできる最も単純なことは、項を正規形にもっていくことです。
数値型の場合を除いて、型`T`の項`t`の正規形は、`T`のコンストラクタの適用の列です。
例えば、リストの正規形は、`List.cons`と`List.nil`の適用の列です。

The function that normalises a term (i.e. brings it into normal form) is
`Lean.Meta.reduce` with type signature

項を正規化する関数（すなわち、正規形にもっていく関数）は、型シグネチャを持つ`Lean.Meta.reduce`です。

```lean
reduce (e : Expr) (explicitOnly skipTypes skipProofs := true) : MetaM Expr
```

We can use it like this:
-/

def someNumber : Nat := (· + 2) $ 3

#eval Expr.const ``someNumber []
-- Lean.Expr.const `someNumber []

#eval reduce (Expr.const ``someNumber [])
-- Lean.Expr.lit (Lean.Literal.natVal 5)
-- #eval reduce (Expr.const ``someNumber []) (explicitOnly := true)
-- #reduce Expr.const ``someNumber []

/-!
Incidentally, this shows that the normal form of a term of type `Nat` is not
always an application of the constructors of `Nat`; it can also be a literal.
Also note that `#eval` can be used not only to evaluate a term, but also to
execute a `MetaM` program.

ところで、これは、型`Nat`の項の正規形が、常に`Nat`のコンストラクタの適用であるとは限らないことを示しています。
リテラルになることもあります。
また、`#eval`は項を評価するだけでなく、`MetaM`プログラムを実行するためにも使用できることに注意してください。

The optional arguments of `reduce` allow us to skip certain parts of an
expression. E.g. `reduce e (explicitOnly := true)` does not normalise any
implicit arguments in the expression `e`. This yields better performance: since
normal forms can be very big, it may be a good idea to skip parts of an
expression that the user is not going to see anyway.

`reduce`のオプション引数を使うと、式の一部をスキップすることができます。
例えば、`reduce e (explicitOnly := true)`は、式`e`の暗黙の引数を正規化しません。
これにより、パフォーマンスが向上します。
正規形は非常に大きくなる可能性があるため、
ユーザーが見るつもりのない式の一部をスキップするのは良い考えかもしれません。

The `#reduce` command is essentially an application of `reduce`:

`#reduce`コマンドは、本質的には`reduce`の適用です。
-/

#reduce someNumber
-- 5

/-!
### Transparency

An ugly but important detail of Lean 4 metaprogramming is that any given
expression does not have a single normal form. Rather, it has a normal form up
to a given *transparency*.

Lean 4のメタプログラミングの醜いが重要な詳細は、
与えられた式には単一の正規形がないということです。
むしろ、与えられた*透明度*までの正規形があります。

A transparency is a value of `Lean.Meta.TransparencyMode`, an enumeration with
four values: `reducible`, `instances`, `default` and `all`. Any `MetaM`
computation has access to an ambient `TransparencyMode` which can be obtained
with `Lean.Meta.getTransparency`.

透明度は、`Lean.Meta.TransparencyMode`という列挙型の値です。
`reducible`、`instances`、`default`、`all`の4つの値があります。
任意の`MetaM`計算は、`Lean.Meta.getTransparency`で取得できる環境の`TransparencyMode`にアクセスできます。

The current transparency determines which constants get unfolded during
normalisation, e.g. by `reduce`. (To unfold a constant means to replace it with
its definition.) The four settings unfold progressively more constants:

現在の透明度は、正規化（例えば、`reduce`）中に展開される定数を決定します。
（定数を展開するとは、その定数をその定義に置き換えることを意味します。）
4つの設定は、徐々により多くの定数を展開します。

- `reducible`: unfold only constants tagged with the `@[reducible]` attribute.
  Note that `abbrev` is a shorthand for `@[reducible] def`.
- `instances`: unfold reducible constants and constants tagged with the
  `@[instance]` attribute. Again, the `instance` command is a shorthand for
  `@[instance] def`.
- `default`: unfold all constants except those tagged as `@[irreducible]`.
- `all`: unfold all constants, even those tagged as `@[irreducible]`.

- `reducible`：`@[reducible]`属性でタグ付けされた定数のみを展開します。
  `abbrev`は`@[reducible] def`の略記法であることに注意してください。
- `instances`：`reducible`定数と`@[instance]`属性でタグ付けされた定数を展開します。
  同様に、`instance`コマンドは`@[instance] def`の略記法です。
- `default`：`@[irreducible]`とタグ付けされた定数を除くすべての定数を展開します。
- `all`：`@[irreducible]`とタグ付けされた定数を含むすべての定数を展開します。

The ambient transparency is usually `default`. To execute an operation with a
specific transparency, use `Lean.Meta.withTransparency`. There are also
shorthands for specific transparencies, e.g. `Lean.Meta.withReducible`.

環境の透明度は通常`default`です。
特定の透明度で操作を実行するには、`Lean.Meta.withTransparency`を使用します。
特定の透明度の略記法もあります。
例えば、`Lean.Meta.withReducible`です。

Putting everything together for an example (where we use `Lean.Meta.ppExpr` to
pretty-print an expression):

すべてをまとめて例を挙げます（`Lean.Meta.ppExpr`を使用して式をきれいに表示します）。
-/

def traceConstWithTransparency (md : TransparencyMode) (c : Name) :
    MetaM Format := do
  ppExpr (← withTransparency md $ reduce (.const c []))

@[irreducible] def irreducibleDef : Nat      := 1
def                defaultDef     : Nat      := irreducibleDef + 1
abbrev             reducibleDef   : Nat      := defaultDef + 1

/-!
We start with `reducible` transparency, which only unfolds `reducibleDef`:

`reducible`透明度から始めます。これは`reducibleDef`のみを展開します。
-/

#eval traceConstWithTransparency .reducible ``reducibleDef
-- defaultDef + 1

/-!
If we repeat the above command but let Lean print implicit arguments as well,
we can see that the `+` notation amounts to an application of the `hAdd`
function, which is a member of the `HAdd` typeclass:

上記のコマンドを繰り返しますが、Leanに暗黙の引数も表示させると、
`+`表記は`HAdd`型クラスのメンバーである`hAdd`関数の適用に相当することがわかります。
-/

-- set_option pp.explicit true in
#eval traceConstWithTransparency .reducible ``reducibleDef
-- @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) defaultDef 1

/-!
When we reduce with `instances` transparency, this applications is unfolded and
replaced by `Nat.add`:

`instances`透明度で縮小すると、このアプリケーションは展開されて`Nat.add`に置き換えられます。
-/

#eval traceConstWithTransparency .instances ``reducibleDef
-- Nat.add defaultDef 1

/-!
With `default` transparency, `Nat.add` is unfolded as well:

`default`透明度では、`Nat.add`も展開されます。
-/

#eval traceConstWithTransparency .default ``reducibleDef
-- Nat.succ (Nat.succ irreducibleDef)

/-!
And with `TransparencyMode.all`, we're finally able to unfold `irreducibleDef`:

そして、`TransparencyMode.all`で、`irreducibleDef`を展開できるようになりました。
-/

#eval traceConstWithTransparency .all ``reducibleDef
-- 3

/-!
The `#eval` commands illustrate that the same term, `reducibleDef`, can have a
different normal form for each transparency.

`#eval`コマンドは、同じ項`reducibleDef`が、透明度ごとに異なる正規形を持つことを示しています。

Why all this ceremony? Essentially for performance: if we allowed normalisation
to always unfold every constant, operations such as type class search would
become prohibitively expensive. The tradeoff is that we must choose the
appropriate transparency for each operation that involves normalisation.

なぜこのような儀式が必要なのでしょうか？基本的にはパフォーマンスのためです。
正規化が常にすべての定数を展開することを許可した場合、
型クラス検索などの操作は非常に高価になります。
トレードオフは、正規化を含む各操作に適切な透明度を選択する必要があることです。


### Weak Head Normalisation

Transparency addresses some of the performance issues with normalisation. But
even more important is to recognise that for many purposes, we don't need to
fully normalise terms at all. Suppose we are building a tactic that
automatically splits hypotheses of the type `P ∧ Q`. We might want this tactic
to recognise a hypothesis `h : X` if `X` reduces to `P ∧ Q`. But if `P`
additionally reduces to `Y ∨ Z`, the specific `Y` and `Z` do not concern us.
Reducing `P` would be unnecessary work.

透明度は、正規化に関するいくつかのパフォーマンスの問題に対処します。
しかし、さらに重要なのは、多くの目的において、項を完全に正規化する必要がないことを認識することです。
`P ∧ Q`の型の仮説を自動的に分割するタクティックを構築しているとします。
`X`が`P ∧ Q`に簡約される場合、このタクティックは仮説`h : X`を認識することを望むかもしれません。
しかし、`P`が`Y ∨ Z`にさらに簡約される場合、特定の`Y`と`Z`は私たちに関係しません。
`P`を簡約することは不要な作業になります。

This situation is so common that the fully normalising `reduce` is in fact
rarely used. Instead, the normalisation workhorse of Lean is `whnf`, which
reduces an expression to *weak head normal form* (WHNF).

この状況は非常に一般的であるため、完全に正規化された`reduce`は実際にはめったに使用されません。
代わりに、Leanの正規化の作業馬は`whnf`です。
これは式を*弱頭部正規形*（WHNF）に簡約します。

Roughly speaking, an expression `e` is in weak-head normal form when it has the
form

おおよそ言えば、式`e`は、次の形式のときに弱頭部正規形になります。

```text
e = f x₁ ... xₙ   (n ≥ 0)
```

and `f` cannot be reduced (at the current transparency). To conveniently check
the WHNF of an expression, we define a function `whnf'`, using some functions
that will be discussed in the Elaboration chapter.

`f`は（現在の透明度では）簡約できないとします。
式のWHNFを便利にチェックするために、いくつかの関数を使用して関数`whnf'`を定義します。
これらの関数は、Elaboration章で説明します。
-/

open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) : TermElabM Format := do
  let e ← elabTermAndSynthesize (← e) none
  ppExpr (← whnf e)

/-!
Now, here are some examples of expressions in WHNF.

Constructor applications are in WHNF (with some exceptions for numeric types):

ここで、WHNFの式のいくつかの例を示します。

コンストラクタの適用はWHNFです（数値型の場合を除く）。
-/

#eval whnf' `(List.cons 1 [])
-- [1]

/-!
The *arguments* of an application in WHNF may or may not be in WHNF themselves:

WHNFのアプリケーションの*引数*は、それ自体がWHNFであるかどうかは問題ではありません。
-/
#eval whnf' `(List.cons (1 + 1) [])
-- [1 + 1]

/-!
Applications of constants are in WHNF if the current transparency does not
allow us to unfold the constants:

定数の適用は、現在の透明度が定数を展開することを許可しない場合、WHNFです。
-/

#eval withTransparency .reducible $ whnf' `(List.append [1] [2])
-- List.append [1] [2]

/-!
Lambdas are in WHNF:

ラムダはWHNFです。
-/

#eval whnf' `(λ x : Nat => x)
-- fun x => x

/-!
Foralls are in WHNF:

ForallもWHNFです。
-/

#eval whnf' `(∀ x, x > 0)
-- ∀ (x : Nat), x > 0

/-!
Sorts are in WHNF:

ソートもWHNFです。
-/

#eval whnf' `(Type 3)
-- Type 3

/-!
Literals are in WHNF:

リテラルもWHNFです。
-/

#eval whnf' `((15 : Nat))
-- 15

/-!
Here are some more expressions in WHNF which are a bit tricky to test:

さらにいくつかのWHNFの式をテストするのは少し難しいです。

```lean
?x 0 1  -- Assuming the metavariable `?x` is unassigned, it is in WHNF.
h 0 1   -- Assuming `h` is a local hypothesis, it is in WHNF.
```

On the flipside, here are some expressions that are not in WHNF.

反対に、WHNFではない式もいくつかあります。

Applications of constants are not in WHNF if the current transparency allows us
to unfold the constants:

定数の適用は、現在の透明度が定数を展開することを許可する場合、WHNFではありません。
-/

#eval whnf' `(List.append [1])
-- fun x => 1 :: List.append [] x

/-!
Applications of lambdas are not in WHNF:

ラムダの適用はWHNFではありません。
-/

#eval whnf' `((λ x y : Nat => x + y) 1)
-- `fun y => 1 + y`

/-!
`let` bindings are not in WHNF:

`let`束縛はWHNFではありません。
-/

#eval whnf' `(let x : Nat := 1; x)
-- 1

/-!
And again some tricky examples:

そして、再びいくつかのトリッキーな例です。

```lean
?x 0 1 -- Assuming `?x` is assigned (e.g. to `Nat.add`), its application is not
          in WHNF.
h 0 1  -- Assuming `h` is a local definition (e.g. with value `Nat.add`), its
          application is not in WHNF.
```

Returning to the tactic that motivated this section, let us write a function
that matches a type of the form `P ∧ Q`, avoiding extra computation. WHNF
makes it easy:

このセクションの動機付けとなったタクティックに戻り、
余分な計算を避けて`P ∧ Q`の形の型に一致する関数を書いてみましょう。
WHNFを使うと簡単です。
-/

def matchAndReducing (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) Q) => return some (P, Q)
  | _ => return none

/-
By using `whnf`, we ensure that if `e` evaluates to something of the form `P
∧ Q`, we'll notice. But at the same time, we don't perform any unnecessary
computation in `P` or `Q`.

`whnf`を使用することで、`e`が`P ∧ Q`の形のものに評価される場合、
それに気づくことができます。
しかし、同時に、`P`または`Q`で不必要な計算を行いません。

However, our 'no unnecessary computation' mantra also means that if we want to
perform deeper matching on an expression, we need to use `whnf` multiple times.
Suppose we want to match a type of the form `P ∧ Q ∧ R`. The correct way to do
this uses `whnf` twice:

しかし、'不必要な計算はしない'という私たちのマントラは、
式により深いマッチングを行う場合には、複数回`whnf`を使用する必要があることを意味します。
`P ∧ Q ∧ R`の形の型に一致する方法は、`whnf`を2回使用することです。
-/

def matchAndReducing₂ (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) e') =>
    match ← whnf e' with
    | (.app (.app (.const ``And _) Q) R) => return some (P, Q, R)
    | _ => return none
  | _ => return none

/-!
This sort of deep matching up to computation could be automated. But until
someone builds this automation, we have to figure out the necessary `whnf`s
ourselves.

このような計算による深いマッチングは自動化できます。
しかし、誰かがこの自動化を構築するまで、必要な`whnf`を自分で考えなければなりません。


### Definitional Equality

As mentioned, definitional equality is equality up to computation. Two
expressions `t` and `s` are definitionally equal or *defeq* (at the current
transparency) if their normal forms (at the current transparency) are equal.

前述のように、定義的等価性は計算による等価性です。
2つの式`t`と`s`は、正規形（現在の透明度で）が等しい場合、定義的に等しいまたは*defeq*（現在の透明度で）です。

To check whether two expressions are defeq, use `Lean.Meta.isDefEq` with type
signature

2つの式がdefeqであるかどうかを確認するには、型シグネチャを使用して`Lean.Meta.isDefEq`を使用します。

```lean
isDefEq : Expr → Expr → MetaM Bool
```

Even though definitional equality is defined in terms of normal forms, `isDefEq`
does not actually compute the normal forms of its arguments, which would be very
expensive. Instead, it tries to "match up" `t` and `s` using as few reductions
as possible. This is a necessarily heuristic endeavour and when the heuristics
misfire, `isDefEq` can become very expensive. In the worst case, it may have to
reduce `s` and `t` so often that they end up in normal form anyway. But usually
the heuristics are good and `isDefEq` is reasonably fast.

定義的等価性は正規形に基づいて定義されていますが、`isDefEq`は、
非常に高価な引数の正規形を実際に計算しません。
代わりに、できるだけ少ない簡約を使用して`t`と`s`を「マッチさせよう」とします。
これは必然的にヒューリスティックな取り組みであり、ヒューリスティックが誤作動すると、
`isDefEq`は非常に高価になる可能性があります。
最悪の場合、`s`と`t`を何度も簡約しなければならず、結局は正規形になってしまうかもしれません。
しかし、通常、ヒューリスティックは良く、`isDefEq`はかなり高速です。

If expressions `t` and `u` contain assignable metavariables, `isDefEq` may
assign these metavariables to make `t` defeq to `u`. We also say that `isDefEq`
*unifies* `t` and `u`; such unification queries are sometimes written `t =?= u`.
For instance, the unification `List ?m =?= List Nat` succeeds and assigns `?m :=
Nat`. The unification `Nat.succ ?m =?= n + 1` succeeds and assigns `?m := n`.
The unification `?m₁ + ?m₂ + ?m₃ =?= m + n - k` fails and no metavariables are
assigned (even though there is a 'partial match' between the expressions).

式`t`と`u`に割り当て可能なメタ変数が含まれている場合、`isDefEq`はこれらのメタ変数を割り当てて、
`t`を`u`にdefeqすることができます。
また、`isDefEq`は`t`と`u`を*unify*します。
このようなunificationクエリは、`t =?= u`と書かれることがあります。
例えば、unification`List ?m =?= List Nat`は成功し、`?m := Nat`を割り当てます。
unification`Nat.succ ?m =?= n + 1`は成功し、`?m := n`を割り当てます。
unification`?m₁ + ?m₂ + ?m₃ =?= m + n - k`は失敗し、メタ変数は割り当てられません
（式の間に「部分的な一致」があるにもかかわらず）。

Whether `isDefEq` considers a metavariable assignable is determined by two
factors:

`isDefEq`がメタ変数を割り当て可能とみなすかどうかは、2つの要因によって決まります。

1. The metavariable's depth must be equal to the current `MetavarContext` depth.
   See the [Metavariable Depth section](#metavariable-depth).
2. Each metavariable has a *kind* (a value of type `MetavarKind`) whose sole
   purpose is to modify the behaviour of `isDefEq`. Possible kinds are:
   - Natural: `isDefEq` may freely assign the metavariable. This is the default.
   - Synthetic: `isDefEq` may assign the metavariable, but avoids doing so if
     possible. For example, suppose `?n` is a natural metavariable and `?s` is a
     synthetic metavariable. When faced with the unification problem
     `?s =?= ?n`, `isDefEq` assigns `?n` rather than `?s`.
   - Synthetic opaque: `isDefEq` never assigns the metavariable.

1. メタ変数の深さは、現在の`MetavarContext`の深さと等しくなければなりません。
    [Metavariable Depth section](#metavariable-depth)を参照してください。
2. 各メタ変数には*種類*（`MetavarKind`型の値）があり、その唯一の目的は 
    `isDefEq` の振る舞いを変更することです。可能な種類は次のとおりです。
    - Natural：`isDefEq`はメタ変数を自由に割り当てることができます。これがデフォルトです。
    - Synthetic: `isDefEq`はメタ変数を割り当てることができますが、可能な限り割り当てないようにします。
        例えば、`?n`が自然なメタ変数であり、`?s`が合成メタ変数であるとします。
        `?s =?= ?n`というunification問題に直面したとき、`isDefEq`は`?s`ではなく`?n`を割り当てます。
    - Synthetic opaque: `isDefEq`はメタ変数を割り当てません。

## Constructing Expressions

In the previous chapter, we saw some primitive functions for building
expressions: `Expr.app`, `Expr.const`, `mkAppN` and so on. There is nothing
wrong with these functions, but the additional facilities of `MetaM` often
provide more convenient ways.

前の章では、式を構築するためのいくつかの基本的な関数を見ました。
`Expr.app`、`Expr.const`、`mkAppN`などです。
これらの関数に問題はありませんが、`MetaM`の追加の機能は、
より便利な方法を提供することが多いです。


### Applications

When we write regular Lean code, Lean helpfully infers many implicit arguments
and universe levels. If it did not, our code would look rather ugly:

通常のLeanコードを書くとき、Leanは多くの暗黙の引数と宇宙レベルを便利に推論してくれます。
そうしないと、コードはかなり醜く見えます。
 -/

def appendAppend (xs ys : List α) := (xs.append ys).append xs

set_option pp.all true in
set_option pp.explicit true in
#print appendAppend
-- def appendAppend.{u_1} : {α : Type u_1} → List.{u_1} α → List.{u_1} α → List.{u_1} α :=
-- fun {α : Type u_1} (xs ys : List.{u_1} α) => @List.append.{u_1} α (@List.append.{u_1} α xs ys) xs

/-!
The `.{u_1}` suffixes are universe levels, which must be given for every
polymorphic constant. And of course the type `α` is passed around everywhere.

`.{u_1}` の接尾辞は宇宙レベルで、すべての多相定数に対して与える必要があります。
そして、もちろん型`α`はどこにでも渡されます。

Exactly the same problem occurs during metaprogramming when we construct
expressions. A hand-made expression representing the right-hand side of the
above definition looks like this:

同じ問題が、式を構築するときにメタプログラミング中に発生します。
上記の定義の右辺を表す手作りの式は、次のようになります。
-/

def appendAppendRHSExpr₁ (u : Level) (α xs ys : Expr) : Expr :=
  mkAppN (.const ``List.append [u])
    #[α, mkAppN (.const ``List.append [u]) #[α, xs, ys], xs]

/-!
Having to specify the implicit arguments and universe levels is annoying and
error-prone. So `MetaM` provides a helper function which allows us to omit
implicit information: `Lean.Meta.mkAppM` of type

暗黙の引数と宇宙レベルを指定する必要があるのは面倒でエラーが発生しやすいです。
そこで、`MetaM`は、暗黙の情報を省略できるようにするヘルパー関数を提供します。
型`Lean.Meta.mkAppM`の

```lean
mkAppM : Name → Array Expr → MetaM Expr
```

Like `mkAppN`, `mkAppM` constructs an application. But while `mkAppN` requires
us to give all universe levels and implicit arguments ourselves, `mkAppM` infers
them. This means we only need to provide the explicit arguments, which makes for
a much shorter example:

`mkAppN`と同様に、`mkAppM`はアプリケーションを構築します。
しかし、`mkAppN`はすべての宇宙レベルと暗黙の引数を自分で指定する必要がありますが、
`mkAppM`はそれらを推論します。
これは、明示的な引数のみを指定すればよいことを意味します。
これにより、はるかに短い例が得られます。
-/

def appendAppendRHSExpr₂ (xs ys : Expr) : MetaM Expr := do
  mkAppM ``List.append #[← mkAppM ``List.append #[xs, ys], xs]

/-!
Note the absence of any `α`s and `u`s. There is also a variant of `mkAppM`,
`mkAppM'`, which takes an `Expr` instead of a `Name` as the first argument,
allowing us to construct applications of expressions which are not constants.

`α`と`u`がないことに注意してください。
`mkAppM`の変種には、最初の引数として`Name`の代わりに`Expr`を取る`mkAppM'`もあります。
これにより、定数でない式のアプリケーションを構築することができます。

However, `mkAppM` is not magic: if you write `mkAppM ``List.append #[]`, you
will get an error at runtime. This is because `mkAppM` tries to determine what
the type `α` is, but with no arguments given to `append`, `α` could be anything,
so `mkAppM` fails.

しかし、`mkAppM`は魔法ではありません。
`mkAppM ``List.append #[]`と書くと、実行時にエラーが発生します。
これは、`mkAppM`が型`α`が何であるかを決定しようとするが、
`append`に引数が与えられていないため、`α`は何でもあり得るため、`mkAppM`が失敗するからです。

Another occasionally useful variant of `mkAppM` is `Lean.Meta.mkAppOptM` of type

`mkAppM`のたまに便利な変種は、型の`Lean.Meta.mkAppOptM`です。

```lean
mkAppOptM : Name → Array (Option Expr) → MetaM Expr
```

Whereas `mkAppM` always infers implicit and instance arguments and always
requires us to give explicit arguments, `mkAppOptM` lets us choose freely which
arguments to provide and which to infer. With this, we can, for example, give
instances explicitly, which we use in the following example to give a
non-standard `Ord` instance.

`mkAppM`は常に暗黙の引数とインスタンス引数を推論し、常に明示的な引数を指定する必要がありますが、
`mkAppOptM`は、どの引数を指定し、どの引数を推論するかを自由に選択できます。
これにより、例えば、インスタンスを明示的に与えることができます。
次の例では、非標準の`Ord`インスタンスを与えるために使用します。
-/

def revOrd : Ord Nat where
  compare x y := compare y x

def ordExpr : MetaM Expr := do
  mkAppOptM ``compare #[none, Expr.const ``revOrd [], mkNatLit 0, mkNatLit 1]

#eval format <$> ordExpr
-- Ord.compare.{0} Nat revOrd
--   (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
--   (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))

/-!
Like `mkAppM`, `mkAppOptM` has a primed variant `Lean.Meta.mkAppOptM'` which
takes an `Expr` instead of a `Name` as the first argument. The file which
contains `mkAppM` also contains various other helper functions, e.g. for making
list literals or `sorry`s.

`mkAppM`と同様に、`mkAppOptM`には、最初の引数として`Name`の代わりに
`Expr`を取る`Lean.Meta.mkAppOptM'`という変種があります。
`mkAppM`を含むファイルには、リストリテラルや`sorry`を作成するための
さまざまなヘルパー関数も含まれています。


### Lambdas and Foralls

Another common task is to construct expressions involving `λ` or `∀` binders.
Suppose we want to create the expression `λ (x : Nat), Nat.add x x`. One way is
to write out the lambda directly:

もう一つの一般的なタスクは、`λ`または`∀`バインダを含む式を構築することです。
式`λ (x : Nat), Nat.add x x`を作成したいとします。
一つの方法は、ラムダを直接書くことです。
-/

def doubleExpr₁ : Expr :=
  .lam `x (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[.bvar 0, .bvar 0])
    BinderInfo.default

#eval ppExpr doubleExpr₁
-- fun x => Nat.add x x

/-!
This works, but the use of `bvar` is highly unidiomatic. Lean uses a so-called
*locally closed* variable representation. This means that all but the
lowest-level functions in the Lean API expect expressions not to contain 'loose
`bvar`s', where a `bvar` is loose if it is not bound by a binder in the same
expression. (Outside of Lean, such variables are usually called 'free'. The name
`bvar` -- 'bound variable' -- already indicates that `bvar`s are never supposed
to be free.)

これは動作しますが、`bvar`の使用は非常に非常識的です。
Leanは、*locally closed*変数表現を使用しています。
これは、Lean APIの最下位レベルの関数を除いて、
すべての関数が、同じ式の束縛によって束縛されていない場合、
式に'loose `bvar`'を含まないことを期待していることを意味します。
（Leanの外では、このような変数は通常「free」と呼ばれます。
`bvar`という名前は、`bvar`が決してfreeにならないことをすでに示しています。）

As a result, if in the above example we replace `mkAppN` with the slightly
higher-level `mkAppM`, we get a runtime error. Adhering to the locally closed
convention, `mkAppM` expects any expressions given to it to have no loose bound
variables, and `.bvar 0` is precisely that.

その結果、上記の例で`mkAppN`を少し上位レベルの`mkAppM`に置き換えると、
実行時エラーが発生します。
ローカルクローズド規則に従うと、`mkAppM`は、
それに与えられた式に束縛されていない変数がないことを期待しています。
そして、`.bvar 0`はまさにそれです。

So instead of using `bvar`s directly, the Lean way is to construct expressions
with bound variables in two steps:

そのため、`bvar`を直接使用する代わりに、
Leanの方法は、束縛変数を含む式を2つのステップで構築することです。

1. Construct the body of the expression (in our example: the body of the
   lambda), using temporary local hypotheses (`fvar`s) to stand in for the bound
   variables.
2. Replace these `fvar`s with `bvar`s and, at the same time, add the
   corresponding lambda binders.

1. 式の本体（この例ではラムダの本体）を構築し、
    仮のローカル仮説（`fvar`）を束縛変数の代わりに使用します。
2. これらの`fvar`を`bvar`に置き換え、同時に対応するラムダバインダを追加します。

This process ensures that we do not need to handle expressions with loose
`bvar`s at any point (except during step 2, which is performed 'atomically' by a
bespoke function). Applying the process to our example:

このプロセスにより、ステップ2（専用の関数により「アトミックに」実行される）を除いて、
いつでもloose `bvar`を含む式を処理する必要がなくなります。
私たちの例にこのプロセスを適用すると、
-/

def doubleExpr₂ : MetaM Expr :=
  withLocalDecl `x BinderInfo.default (.const ``Nat []) λ a => do
    let body ← mkAppM ``Nat.add #[a, a]
    -- return body
    mkLambdaFVars #[a] body

#eval show MetaM _ from do
  ppExpr (← doubleExpr₂)
-- fun x => Nat.add x x

/-!
There are two new functions. First, `Lean.Meta.withLocalDecl` has type

新しい関数が2つあります。
まず、`Lean.Meta.withLocalDecl`の型は

```lean
withLocalDecl (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → MetaM α) : MetaM α
```

Given a variable name, binder info and type, `withLocalDecl` constructs a new
`fvar` and passes it to the computation `k`. The `fvar` is available in the local
context during the execution of `k` but is deleted again afterwards.

変数名、バインダ情報、型が与えられた場合、`withLocalDecl`は新しい`fvar`を構築し、
計算`k`に渡します。
`fvar`は、`k`の実行中にローカルコンテキストで使用できますが、
その後削除されます。

The second new function is `Lean.Meta.mkLambdaFVars` with type (ignoring some
optional arguments)

2番目の新しい関数は、型`Lean.Meta.mkLambdaFVars`です（いくつかのオプション引数を無視しています）
```
mkLambdaFVars : Array Expr → Expr → MetaM Expr
```

This function takes an array of `fvar`s and an expression `e`. It then adds one
lambda binder for each `fvar` `x` and replaces every occurrence of `x` in `e`
with a bound variable corresponding to the new lambda binder. The returned
expression does not contain the `fvar`s any more, which is good since they
disappear after we leave the `withLocalDecl` context. (Instead of `fvar`s, we
can also give `mvar`s to `mkLambdaFVars`, despite its name.)

この関数は、`fvar`の配列と式`e`を取ります。
そして、`fvar` `x`ごとに1つのラムダバインダを追加し、
`e`のすべての出現を、新しいラムダバインダに対応する束縛変数で置き換えます。
返される式にはもはや`fvar`は含まれていませんが、
これは`withLocalDecl`コンテキストを離れた後に消えるので、良いことです。
（`mkLambdaFVars`には、名前にもかかわらず、`fvar`の代わりに`mvar`を与えることもできます。）

Some variants of the above functions may be useful:

上記の関数のいくつかの変種は便利です。

- `withLocalDecls` declares multiple temporary `fvar`s.
- `mkForallFVars` creates `∀` binders instead of `λ` binders. `mkLetFVars`
  creates `let` binders.
- `mkArrow` is the non-dependent version of `mkForallFVars` which construcs
  a function type `X → Y`. Since the type is non-dependent, there is no need
  for temporary `fvar`s.

- `withLocalDecls`は複数の一時的な`fvar`を宣言します。
- `mkForallFVars`は`λ`バインダの代わりに`∀`バインダを作成します。
    `mkLetFVars`は`let`バインダを作成します。
- `mkArrow`は、関数型`X → Y`を構築する`mkForallFVars`の非依存バージョンです。
    型が非依存であるため、一時的な`fvar`は必要ありません。

Using all these functions, we can construct larger expressions such as this one:

これらのすべての関数を使用すると、次のような大きな式を構築できます。

```lean
λ (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)
```
-/

def somePropExpr : MetaM Expr := do
  let funcType ← mkArrow (.const ``Nat []) (.const ``Nat [])
  withLocalDecl `f BinderInfo.default funcType fun f => do
    let feqn ← withLocalDecl `n BinderInfo.default (.const ``Nat []) fun n => do
      let lhs := .app f n
      let rhs := .app f (← mkAppM ``Nat.succ #[n])
      let eqn ← mkEq lhs rhs
      mkForallFVars #[n] eqn
    mkLambdaFVars #[f] feqn

/-!
The next line registers `someProp` as a name for the expression we've just
constructed, allowing us to play with it more easily. The mechanisms behind this
are discussed in the Elaboration chapter.

次の行は、`someProp`を、私たちが作成した式の名前として登録します。
これにより、より簡単に操作できます。
これに関するメカニズムは、Elaboration章で説明します。
-/

elab "someProp" : term => somePropExpr

#check someProp
-- fun f => ∀ (n : Nat), f n = f (Nat.succ n) : (Nat → Nat) → Prop
#reduce someProp Nat.succ
-- ∀ (n : Nat), Nat.succ n = Nat.succ (Nat.succ n)


/-!
### Deconstructing Expressions

Just like we can construct expressions more easily in `MetaM`, we can also
deconstruct them more easily. Particularly useful is a family of functions for
deconstructing expressions which start with `λ` and `∀` binders.

`MetaM`で式をより簡単に構築できるようにするのと同様に、
式をより簡単に分解することもできます。
特に便利なのは、`λ`と`∀`バインダで始まる式を分解するための関数のファミリーです。

When we are given a type of the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, we are
often interested in doing something with the conclusion `U`. For instance, the
`apply` tactic, when given an expression `e : ∀ ..., U`, compares `U` with the
current target to determine whether `e` can be applied.

型`∀ (x₁ : T₁) ... (xₙ : Tₙ), U`の形式の式が与えられたとき、
私たちはしばしば結論`U`を使って何かをすることに興味があります。
例えば、`apply`タクティックは、式`e : ∀ ..., U`が与えられたとき、
`U`を現在のターゲットと比較して、`e`を適用できるかどうかを決定します。

To do this, we could repeatedly match on the type expression, removing `∀`
binders until we get to `U`. But this would leave us with an `U` containing
unbound `bvar`s, which, as we saw, is bad. Instead, we use
`Lean.Meta.forallTelescope` of type

これを行うには、型式に繰り返しマッチし、`U`に到達するまで`∀`バインダを削除します。
しかし、これにより、`U`には束縛されていない`bvar`が含まれるため、
前述のように、これは良くありません。
代わりに、型`Lean.Meta.forallTelescope`を使用します。

```
forallTelescope (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α
```

Given `type = ∀ (x₁ : T₁) ... (xₙ : Tₙ), U x₁ ... xₙ`, this function creates one
fvar `fᵢ` for each `∀`-bound variable `xᵢ` and replaces each `xᵢ` with `fᵢ` in
the conclusion `U`. It then calls the computation `k`, passing it the `fᵢ` and
the conclusion `U f₁ ... fₙ`. Within this computation, the `fᵢ` are registered
in the local context; afterwards, they are deleted again (similar to
`withLocalDecl`).

`type = ∀ (x₁ : T₁) ... (xₙ : Tₙ), U x₁ ... xₙ`が与えられた場合、
この関数は、`∀`-bound変数`xᵢ`ごとに1つの`fvar` `fᵢ`を作成し、
結論`U`の`xᵢ`を`fᵢ`で置き換えます。
そして、計算`k`を呼び出し、`fᵢ`と結論`U f₁ ... fₙ`を渡します。
この計算の中で、`fᵢ`はローカルコンテキストに登録されます。
その後、それらは削除されます（`withLocalDecl`と同様）。

There are many useful variants of `forallTelescope`:

`forallTelescope`には、多くの便利な変種があります。

- `forallTelescopeReducing`: like `forallTelescope` but matching is performed up
  to computation. This means that if you have an expression `X` which is
  different from but defeq to `∀ x, P x`, `forallTelescopeReducing X` will
  deconstruct `X` into `x` and `P x`. The non-reducing `forallTelescope` would
  not recognise `X` as a quantified expression. The matching is performed by
  essentially calling `whnf` repeatedly, using the ambient transparency.
- `forallBoundedTelescope`: like `forallTelescopeReducing` (even though there is
  no "reducing" in the name) but stops after a specified number of `∀` binders.
- `forallMetaTelescope`, `forallMetaTelescopeReducing`,
  `forallMetaBoundedTelescope`: like the corresponding non-`meta` functions, but
  the bound variables are replaced by new `mvar`s instead of `fvar`s. Unlike the
  non-`meta` functions, the `meta` functions do not delete the new metavariables
  after performing some computation, so the metavariables remain in the
  environment indefinitely.
- `lambdaTelescope`, `lambdaTelescopeReducing`, `lambdaBoundedTelescope`,
  `lambdaMetaTelescope`: like the corresponding `forall` functions, but for
  `λ` binders instead of `∀`.

- `forallTelescopeReducing`：`forallTelescope`と同様ですが、マッチングは計算まで行われます。
    これは、`∀ x、P x`とは異なるが`defeq`である式`X`がある場合、
    `forallTelescopeReducing X`は`X`を`x`と`P x`に分解します。
    非縮小`forallTelescope`は、`X`を量子化された式として認識しません。
    マッチングは、本質的には、環境透明性を使用して`whnf`を繰り返し呼び出すことによって行われます。
- `forallBoundedTelescope`：`forallTelescopeReducing`と同様です（名前に「reducing」はありません）が、
    指定された数の`∀`バインダー後に停止します。
- `forallMetaTelescope`、`forallMetaTelescopeReducing`、`forallMetaBoundedTelescope`：
    対応する非`meta`関数と同様ですが、束縛変数は`fvar`の代わりに新しい`mvar`で置き換えられます。
    非`meta`関数とは異なり、`meta`関数は、いくつかの計算を実行した後に新しいメタ変数を削除しないため、
    メタ変数は環境に無期限に残ります。
- `lambdaTelescope`、`lambdaTelescopeReducing`、`lambdaBoundedTelescope`、`lambdaMetaTelescope`：
    `∀`の代わりに`λ`バインダーを使用する対応する`forall`関数です。

Using one of the telescope functions, we can implement our own `apply` tactic:

テレスコープ関数の1つを使用して、独自の`apply`タクティックを実装できます。
-/

def myApply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  -- Check that the goal is not yet assigned.
  goal.checkNotAssigned `myApply
  -- Operate in the local context of the goal.
  goal.withContext do
    -- Get the goal's target type.
    let target ← goal.getType
    -- Get the type of the given expression.
    let type ← inferType e
    -- If `type` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce new
    -- metavariables for the `xᵢ` and obtain the conclusion `U`. (If `type` does
    -- not have this form, `args` is empty and `conclusion = type`.)
    let (args, _, conclusion) ← forallMetaTelescopeReducing type
    -- If the conclusion unifies with the target:
    if ← isDefEq target conclusion then
      -- Assign the goal to `e x₁ ... xₙ`, where the `xᵢ` are the fresh
      -- metavariables in `args`.
      goal.assign (mkAppN e args)
      -- `isDefEq` may have assigned some of the `args`. Report the rest as new
      -- goals.
      let newGoals ← args.filterMapM λ mvar => do
        let mvarId := mvar.mvarId!
        if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
          return some mvarId
        else
          return none
      return newGoals.toList
    -- If the conclusion does not unify with the target, throw an error.
    else
      throwTacticEx `myApply goal m!"{e} is not applicable to goal with target {target}"

/-!
The real `apply` does some additional pre- and postprocessing, but the core
logic is what we show here. To test our tactic, we need an elaboration
incantation, more about which in the Elaboration chapter.

本当の`apply`は、いくつかの追加の前処理と後処理を行いますが、
ここで示したのは、そのコアロジックです。
私たちのタクティックをテストするには、Elaboration章で説明するよりも
詳細なエラボレーションの呪文が必要です。
-/

elab "myApply" e:term : tactic => do
  let e ← Elab.Term.elabTerm e none
  Elab.Tactic.liftMetaTactic (myApply · e)

example (h : α → β) (a : α) : β := by
  myApply h
  myApply a


/-!

## Backtracking

Many tactics naturally require backtracking: the ability to go back to a
previous state, as if the tactic had never been executed. A few examples:

多くのタクティクは自然にバックトラックを必要とします。
つまり、タクティクが実行されていないかのように、
以前の状態に戻る機能です。
いくつかの例：

- `first | t | u` first executes `t`. If `t` fails, it backtracks and executes
  `u`.
- `try t` executes `t`. If `t` fails, it backtracks to the initial state,
  erasing any changes made by `t`.
- `trivial` attempts to solve the goal using a number of simple tactics
  (e.g. `rfl` or `contradiction`). After each unsuccessful application of such a
  tactic, `trivial` backtracks.

- `first | t | u`は最初に`t`を実行します。
    `t`が失敗した場合、バックトラックして`u`を実行します。
- `try t`は`t`を実行します。
    `t`が失敗した場合、初期状態に戻り、`t`によって行われた変更を消去します。
- `trivial`は、いくつかの単純なタクティック（`rfl`や`contradiction`など）を使用して、
    ゴールを解決しようとします。
    そのようなタクティックの各失敗した適用の後、`trivial`はバックトラックします。

Good thing, then, that Lean's core data structures are designed to enable easy
and efficient backtracking. The corresponding API is provided by the
`Lean.MonadBacktrack` class. `MetaM`, `TermElabM` and `TacticM` are all
instances of this class. (`CoreM` is not but could be.)

よかったことに、Leanのコアデータ構造は、簡単かつ効率的なバックトラックを可能にするように設計されています。
対応するAPIは、`Lean.MonadBacktrack`クラスによって提供されます。
`MetaM`、`TermElabM`、`TacticM`はすべてこのクラスのインスタンスです。 
（`CoreM`はそうではありませんが、そうである可能性があります。）

`MonadBacktrack` provides two fundamental operations:

`MonadBacktrack`は2つの基本的な操作を提供します。

- `Lean.saveState : m s` returns a representation of the current state, where
  `m` is the monad we are in and `s` is the state type. E.g. for `MetaM`,
  `saveState` returns a `Lean.Meta.SavedState` containing the current
  environment, the current `MetavarContext` and various other pieces of
  information.
- `Lean.restoreState : s → m Unit` takes a previously saved state and restores
  it. This effectively resets the compiler state to the previous point.

- `Lean.saveState : m s`は、現在の状態を表すものを返します。
    `m`は私たちがいるモナドであり、`s`は状態の型です。
    例えば、`MetaM`の場合、`saveState`は、
    現在の環境、現在の`MetavarContext`、およびその他のさまざまな情報を含む
    `Lean.Meta.SavedState`を返します。
- `Lean.restoreState : s → m Unit`は、以前に保存された状態を取り、それを復元します。
    これにより、コンパイラの状態が前のポイントにリセットされます。

With this, we can roll our own `MetaM` version of the `try` tactic:

これで、`try`タクティックの`MetaM`バージョンを作成できます。
-/

def tryM (x : MetaM Unit) : MetaM Unit := do
  let s ← saveState
  try
    x
  catch _ =>
    restoreState s

/-!
We first save the state, then execute `x`. If `x` fails, we backtrack the state.

最初に状態を保存し、次に`x`を実行します。
`x`が失敗した場合、状態をバックトラックします。

The standard library defines many combinators like `tryM`. Here are the most
useful ones:

標準ライブラリは、`tryM`のような多くのコンビネータを定義しています。
最も便利なものは次のとおりです。

- `Lean.withoutModifyingState (x : m α) : m α` executes the action `x`, then
  resets the state and returns `x`'s result. You can use this, for example, to
  check for definitional equality without assigning metavariables:
  ```lean
  withoutModifyingState $ isDefEq x y
  ```
  If `isDefEq` succeeds, it may assign metavariables in `x` and `y`. Using
  `withoutModifyingState`, we can make sure this does not happen.
- `Lean.observing? (x : m α) : m (Option α)` executes the action `x`. If `x`
  succeeds, `observing?` returns its result. If `x` fails (throws an exception),
  `observing?` backtracks the state and returns `none`. This is a more
  informative version of our `tryM` combinator.
- `Lean.commitIfNoEx (x : α) : m α` executes `x`. If `x` succeeds,
  `commitIfNoEx` returns its result. If `x` throws an exception, `commitIfNoEx`
  backtracks the state and rethrows the exception.

- `Lean.withoutModifyingState (x : m α) : m α`は、アクション`x`を実行し、
    状態をリセットして`x`の結果を返します。
    たとえば、メタ変数を割り当てることなく定義的等価性をチェックできます。
    ```lean
    withoutModifyingState $ isDefEq x y
    ```
    `isDefEq`が成功すると、`x`と`y`のメタ変数を割り当てることがあります。
    `withoutModifyingState`を使用すると、これが発生しないことを確認できます。
- `Lean.observing? (x : m α) : m (Option α)`は、アクション`x`を実行します。
    `x`が成功すると、`observing?`はその結果を返します。
    `x`が失敗すると（例外をスローすると）、`observing?`は状態をバックトラックし、`none`を返します。
    これは、私たちの`tryM`コンビネータのより情報量の多いバージョンです。
- `Lean.commitIfNoEx (x : α) : m α`は`x`を実行します。
    `x`が成功すると、`commitIfNoEx`はその結果を返します。
    `x`が例外をスローすると、`commitIfNoEx`は状態をバックトラックし、例外を再スローします。

Note that the builtin `try ... catch ... finally` does not perform any
backtracking. So code which looks like this is probably wrong:

組み込みの`try ... catch ... finally`は、バックトラックを実行しません。
したがって、次のようなコードはおそらく間違っています。

```lean
try
  doSomething
catch e =>
  doSomethingElse
```

The `catch` branch, `doSomethingElse`, is executed in a state containing
whatever modifications `doSomething` made before it failed. Since we probably
want to erase these modifications, we should write instead:

`catch`ブランチ`doSomethingElse`は、`doSomething`が失敗する前に行った変更を含む状態で実行されます。
これらの変更を消去したいと思うのであれば、代わりに次のように書くべきです。

```lean
try
  commitIfNoEx doSomething
catch e =>
  doSomethingElse

```

-/
#check commitIfNoEx

/-
Another `MonadBacktrack` gotcha is that `restoreState` does not backtrack the
*entire* state. Caches, trace messages and the global name generator, among
other things, are not backtracked, so changes made to these parts of the state
are not reset by `restoreState`. This is usually what we want: if a tactic
executed by `observing?` produces some trace messages, we want to see them even
if the tactic fails. See `Lean.Meta.SavedState.restore` and `Lean.Core.restore`
for details on what is and is not backtracked.

もう1つの`MonadBacktrack`の注意点は、`restoreState`が*全体の*状態をバックトラックしないことです。
キャッシュ、トレースメッセージ、グローバル名ジェネレータなどはバックトラックされないため、
状態のこれらの部分に対する変更は、`restoreState`によってリセットされません。
これは通常、私たちが望むことです。
`observing?`によって実行されるタクティックがいくつかのトレースメッセージを生成した場合、
タクティックが失敗してもそれらを見たいと思います。
バックトラックされるものとされないものの詳細については、
`Lean.Meta.SavedState.restore`と`Lean.Core.restore`を参照してください。

In the next chapter, we move towards the topic of elaboration, of which
you've already seen several glimpses in this chapter. We start by discussing
Lean's syntax system, which allows you to add custom syntactic constructs to the
Lean parser.

次の章では、この章でいくつかの一部を見たように、
Elaborationのトピックに向かって進みます。
Leanの構文システムについて説明し、
Leanパーサーにカスタム構文構造を追加できるようにします。

## Exercises
-/
/-
1. [**Metavariables**] Create a metavariable with type `Nat`, and assign to it value `3`.
Notice that changing the type of the metavariable from `Nat` to, for example, 
`String`, doesn't raise any errors - that's why, as was mentioned, 
we must make sure 
*"(a) that `val` must have the target type of `mvarId` and 
  (b) that `val` must only contain `fvars` from the local context of `mvarId`"*.
-/

-- def natExpr: Nat → Expr 
-- | 0     => .const ``Nat.zero []
-- | n + 1 => .app (.const ``Nat.succ []) (natExpr n)

#eval show MetaM Unit from do
  let natvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
  natvar1.mvarId!.assign (mkNatLit 3)
  IO.println s!"{ ← instantiateMVars (natvar1)}"
/-
2. [**Metavariables**] What would 
`instantiateMVars (Lean.mkAppN (Expr.const 'Nat.add []) #[mkNatLit 1, mkNatLit 2])` output?
-/
#eval show MetaM Unit from do
  let var ← instantiateMVars (Lean.mkAppN (Expr.const ``Nat.add []) #[mkNatLit 1, mkNatLit 2])
  IO.println s!"{var}"

/-
3. [**Metavariables**] Fill in the missing lines in the following code.

  ```
  #eval show MetaM Unit from do
    let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
    let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

    -- Create `mvar1` with type `Nat`
    -- let mvar1 ← ...
    -- Create `mvar2` with type `Nat`
    -- let mvar2 ← ...
    -- Create `mvar3` with type `Nat`
    -- let mvar3 ← ...

    -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
    -- ...

    -- Assign `mvar3` to `1`
    -- ...

    -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
    ...
  ```
-/
#eval show MetaM Unit from do
  let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
  let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

  -- Create `mvar1` with type `Nat`
  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
  -- Create `mvar2` with type `Nat`
  let mvar2 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar2)
  -- Create `mvar3` with type `Nat`
  let mvar3 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar3)

  -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
  mvar1.mvarId!.assign <| Lean.mkAppN (Expr.const ``Nat.add []) #[(Lean.mkAppN (Expr.const ``Nat.add []) #[twoExpr, mvar2]), mvar3]
  -- Assign `mvar3` to `1`
  mvar3.mvarId!.assign oneExpr

  -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
  let var ← instantiateMVars mvar1
  IO.println var
/-
4. [**Metavariables**] Consider the theorem `red`, and tactic `explore` below.  
  a) What would be the `type` and `userName` of metavariable `mvarId`?  
  b) What would be the `type`s and `userName`s of all local declarations in this metavariable's local context?  
  Print them all out.

  ```
  elab "explore" : tactic => do
    let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
    let metavarDecl : MetavarDecl ← mvarId.getDecl

    IO.println "Our metavariable"
    -- ...

    IO.println "All of its local declarations"
    -- ...

  theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
    explore
    sorry
  ```
-/
elab "explore" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
  let metavarDecl : MetavarDecl ← mvarId.getDecl

  IO.println "Our metavariable"
  IO.println metavarDecl.type
  IO.println metavarDecl.userName

  IO.println "All of its local declarations"
  for ldecl in metavarDecl.lctx do
    if ldecl.isImplementationDetail then
      continue

    IO.println ldecl.type
    IO.println ldecl.userName
  
theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  explore
  sorry
/-
5. [**Metavariables**] Write a tactic `solve` that proves the theorem `red`.
-/

elab "solve" : tactic => do
  let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
  
  mvarId.withContext do
    let target ← mvarId.getType
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then
        continue
      if ← isDefEq ldecl.type target then
        mvarId.assign ldecl.toExpr

theorem red' (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
  solve

/-
6. [**Computation**] What is the normal form of the following expressions:  
  **a)** `fun x => x` of type `Bool → Bool`  
  **b)** `(fun x => x) ((true && false) || true)` of type `Bool`  
  **c)** `800 + 2` of type `Nat`
-/
def idFun : Bool → Bool := fun x => x

#eval reduce (.const ``idFun [])

def someBool := (fun x => x) ((true && false) || true)

#eval reduce (.const ``someBool [])

def num := 800 + 2
#eval reduce (.const ``num [])

/-
7. [**Computation**] Show that `1` created with `Expr.lit (Lean.Literal.natVal 1)` 
is definitionally equal to an expression created with 
`Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])`.
-/
def onelit : Expr := .lit (Lean.Literal.natVal 1)
def oneExpr : Expr := .app (.const ``Nat.succ []) (.const ``Nat.zero [])
#eval isDefEq onelit oneExpr

/-
8. [**Computation**] Determine whether the following expressions are definitionally equal. 
If `Lean.Meta.isDefEq` succeeds, and it leads to metavariable assignment, write down the assignments.  
  **a)** `5 =?= (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))`  
  **b)** `2 + 1 =?= 1 + 2`  
  **c)** `?a =?= 2`, where `?a` has a type `String`  
  **d)** `?a + Int =?= "hi" + ?b`, where `?a` and `?b` don't have a type  
  **e)** `2 + ?a =?= 3`  
  **f)** `2 + ?a =?= 2 + 1`
-/
def five := 5
def five' := (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))
#eval isDefEq (.const ``five []) (.const ``five [])
-- #eval 5 =?= ((fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z)))
def twoPlusOne := 2 + 1
def onePlusTwo := 1 + 2
#eval reduce (.const ``twoPlusOne [])
#eval isDefEq (.const ``twoPlusOne []) (.const ``onePlusTwo [])
-- #eval isDefEq (2 + 1)  (1 + 2)

--  **c)** `?a =?= 2`, where `?a` has a type `String`  
#eval show MetaM Unit from do
  let a ← mkFreshExprMVar (some (.const ``String [])) (userName := `a)
  let two := mkNatLit 2
  let isEqual ← isDefEq a two
  IO.println isEqual

--  **d)** `?a + Int =?= "hi" + ?b`, where `?a` and `?b` don't have a type  
#eval show MetaM Unit from do
  let a ← mkFreshExprMVar (none) (userName := `a)
  let int := .const ``Int []
  let hi := mkStrLit "hi"
  let b ← mkFreshExprMVar (none) (userName := `b)
  let aPlusInt := mkAppN (.const ``Nat.mul []) #[a, int] --なんだこれ
  let hiPlusB := mkAppN (.const ``Nat.mul []) #[hi, b]
  let isEqual ← isDefEq aPlusInt hiPlusB
  IO.println isEqual

  IO.println s!"a: {← instantiateMVars a}"
  IO.println s!"b: {← instantiateMVars b}"

-- **e)** `2 + ?a =?= 3`  
#eval show MetaM Unit from do
  let a ← mkFreshExprMVar (none) (userName := `a)
  let two := mkNatLit 2
  let three := mkNatLit 3
  let twoPlusA := mkAppN (.const ``Nat.add []) #[two, a]
  let isEqual ← isDefEq twoPlusA three
  IO.println isEqual

-- **f)** `2 + ?a =?= 2 + 1`
#eval show MetaM Unit from do
  let a ← mkFreshExprMVar (none) (userName := `a)
  let two := mkNatLit 2
  let one := mkNatLit 1
  let twoPlusA := mkAppN (.const ``Nat.add []) #[two, a]
  let twoPlusOne := mkAppN (.const ``Nat.add []) #[two, one]
  let isEqual ← isDefEq twoPlusA twoPlusOne
  IO.println isEqual

  IO.println s!"a: {← instantiateMVars a}"


/-
9. [**Computation**] Write down what you expect the following code to output.

```
@[reducible] def reducibleDef     : Nat := 1 -- same as `abbrev`
@[instance] def instanceDef       : Nat := 2 -- same as `instance`
def defaultDef                    : Nat := 3
@[irreducible] def irreducibleDef : Nat := 4

@[reducible] def sum := [reducibleDef, instanceDef, defaultDef, irreducibleDef]

#eval show MetaM Unit from do
  let constantExpr := Expr.const `sum []

  Meta.withTransparency Meta.TransparencyMode.reducible do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  Meta.withTransparency Meta.TransparencyMode.instances do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  Meta.withTransparency Meta.TransparencyMode.default do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  Meta.withTransparency Meta.TransparencyMode.all do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- ...

  let reducedExpr ← Meta.reduce constantExpr
  dbg_trace (← ppExpr reducedExpr) -- ...
```
-/

@[reducible] def reducibleDef'     : Nat := 1 -- same as `abbrev`
@[instance] def instanceDef'       : Nat := 2 -- same as `instance`
def defaultDef'                    : Nat := 3
@[irreducible] def irreducibleDef' : Nat := 4

@[reducible] def sum := [reducibleDef', instanceDef', defaultDef', irreducibleDef']

#eval show MetaM Unit from do
  let constantExpr := Expr.const `sum []

  Meta.withTransparency Meta.TransparencyMode.reducible do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- [1, instanceDef', defaultDef', irreducibleDef']

  Meta.withTransparency Meta.TransparencyMode.instances do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- [1, 2 + defaultDef' + irreducibleDef']

  Meta.withTransparency Meta.TransparencyMode.default do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- 1 + 2 + 3 + irreducibleDef'

  Meta.withTransparency Meta.TransparencyMode.all do
    let reducedExpr ← Meta.reduce constantExpr
    dbg_trace (← ppExpr reducedExpr) -- 1 + 2 + 3 + 4

  let reducedExpr ← Meta.reduce constantExpr
  dbg_trace (← ppExpr reducedExpr) -- 1 + 2 + 3 + irreducibleDef'

/-
10. [**Constructing Expressions**] Create expression `fun x, 1 + x` in two ways:  
  **a)** not idiomatically, with loose bound variables  
    **a)** ルーズな束縛変数を使って、非慣用的に。
  **b)** idiomatically.  
    **b)** 慣用的に。
  In what version can you use `Lean.mkAppN`? In what version can you use `Lean.Meta.mkAppM`?
  どのバージョンで `Lean.mkAppN` を使えるか？どのバージョンで `Lean.Meta.mkAppM` を使えるか？
-/
def onePlus : Expr := 
  .lam `x  (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[mkNatLit 1, .bvar 0]) .default

elab "onePlus" : term => return onePlus
#eval onePlus 3

-- def doubleExpr' : MetaM Expr :=
--   withLocalDecl `x BinderInfo.default (.const ``Nat []) λ x => do
--     let body ← mkAppM ``Nat.add #[x, x]
--     mkLambdaFVars #[x] body

def onePlus' : MetaM Expr := do
  withLocalDecl `x .default (.const ``Nat []) fun x => do
    let one := mkNatLit 1
    let xPlusOne ← mkAppM ``Nat.add #[x, one]
    mkLambdaFVars #[x] xPlusOne

elab "onePlus'" : term => return (← onePlus')
#eval onePlus' 3

/-
11. [**Constructing Expressions**] Create expression `∀ (yellow: Nat), yellow`.
-/
def yellow : Expr := 
  .forallE `yellow (.const ``Nat []) (mkBVar 0) .default

def yellow' : MetaM Expr := do
  withLocalDecl `yellow .default (.const ``Nat []) fun yellow => do
    mkForallFVars #[yellow] yellow

#eval show MetaM _ from do
  ppExpr (← yellow')

/-
12. [**Constructing Expressions**] Create expression `∀ (n : Nat), n = n + 1` in two ways:  
  **a)** not idiomatically, with loose bound variables  
  **b)** idiomatically.  
  In what version can you use `Lean.mkApp3`? In what version can you use `Lean.Meta.mkEq`?
-/

def nPlusOne : Expr := 
  .forallE `n (.const ``Nat []) (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1]) .default

def nPlusOne' : MetaM Expr := do
  withLocalDecl `n .default (.const ``Nat []) fun n => do
    let one := mkNatLit 1
    let nPlusOne ← mkAppM ``Nat.add #[n, one]
    mkForallFVars #[n] nPlusOne
def nEqnPlusOne : MetaM Expr := do
  withLocalDecl `n .default (.const ``Nat []) fun n => do
    let one := mkNatLit 1
    let nPlusOne ← mkAppM ``Nat.add #[n, one]
    let eqn ← mkEq n nPlusOne
    mkForallFVars #[n] eqn

#eval show MetaM _ from do
  ppExpr (← nEqnPlusOne)

/-
13. [**Constructing Expressions**] Create expression
 `fun (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)` idiomatically.
-/

def thirtyThree : MetaM Expr := do 
  let funcType ← mkArrow  (mkConst ``Nat) (mkConst ``Nat)
  withLocalDecl `f .default funcType fun f => do
    let v ← withLocalDecl `n .default (.const ``Nat []) fun n => do
      let one := mkNatLit 1
      let nPlusOne ← mkAppM ``Nat.add #[n, one]
      let fNPlusOne := .app f nPlusOne
      let fN := .app f n
      let eqn ← mkEq fN fNPlusOne
      mkForallFVars #[n] eqn
    mkLambdaFVars #[f] v

#eval show MetaM _ from do
  dbg_trace (← thirtyThree)
  ppExpr (← thirtyThree)

/-
14. [**Constructing Expressions**] What would you expect the output of the following code to be?

```
#eval show Lean.Elab.Term.TermElabM _ from do
  let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
  let expr ← Elab.Term.elabTermAndSynthesize stx none

  let (_, _, conclusion) ← forallMetaTelescope expr
  dbg_trace conclusion -- ...

  let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
  dbg_trace conclusion -- ...

  let (_, _, conclusion) ← lambdaMetaTelescope expr
  dbg_trace conclusion -- ...
```
-/
#eval show Lean.Elab.Term.TermElabM _ from do
  let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
  let expr ← Elab.Term.elabTermAndSynthesize stx none

  let (_, _, conclusion) ← forallMetaTelescope expr
  dbg_trace conclusion -- ...

  let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
  dbg_trace conclusion -- ...

  let (_, _, conclusion) ← lambdaMetaTelescope expr
  dbg_trace conclusion -- ...

/-
15. [**Backtracking**] Check that the expressions `?a + Int` and `"hi" + ?b` 
are definitionally equal with `isDefEq` 
(make sure to use the proper types or `Option.none` for the types of your metavariables!).
Use `saveState` and `restoreState` to revert metavariable assignments.

`?a + Int`と`"hi" + ?b`が`isDefEq`で定義的に等しいことを確認します。
（メタ変数の型には適切な型または`Option.none`を使用してください！）
`saveState`と`restoreState`を使用して、メタ変数の割り当てを元に戻します。
-/

#eval show MetaM Unit from do
  let a ← mkFreshExprMVar (none) (userName := `a)
  let int := .const ``Int []
  let hi := mkStrLit "hi"
  let b ← mkFreshExprMVar (none) (userName := `b)
  let aPlusInt := mkAppN (.const ``Nat.add []) #[a, int] 
  let hiPlusB := mkAppN (.const ``Nat.add []) #[hi, b]

  IO.println s!"a: {← instantiateMVars a}"
  IO.println s!"b: {← instantiateMVars b}"

  let s ← saveState

  let isEqual ← isDefEq aPlusInt hiPlusB
  IO.println isEqual
  IO.println s!"a: {← instantiateMVars a}"
  IO.println s!"b: {← instantiateMVars b}"
    
  restoreState s

  IO.println s!"a: {← instantiateMVars a}"
  IO.println s!"b: {← instantiateMVars b}"