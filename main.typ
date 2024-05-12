#import "template.typ": *
#import "typreset/lib.typ": font, thm-envs
#import "commute.typ": node, arr, commutative-diagram

#show: font.set-font.with(lang: "zh")

#let (theorem, definition, lemma, corollary, proof, proposition, example, convention) = thm-envs.presets()
#let thm-base = thm-envs.thm-base

#show: project.with(
  title: "代数",
  authors: (
    (name: "JoJo", email: "jojoid@duck.com"),
  ),
)

= *初等数论*

== *自然数*

#definition[
  *Peano 公理*

    $1." "0 in NN$

    $2." "op("suc") : NN -> NN_+$

    $3." "op("suc")$ 是单射

    $4.$ $forall N subset NN." "0 in N and (forall n in N." "op("suc")(n) in N) => N = NN.$
]

#theorem[
  *强归纳法*
  $
    forall N subset NN." "0 in N and (forall n in NN". " {0, ... , n} subset N => op("suc")(n) in N)
    => N = NN.
  $
]

#proposition[
  存在无穷多的质数.
]

== *整数*

#definition[
  *同余*
  
  设 $n in ZZ_+$. 定义 $ZZ$ 上的二元关系
  $
    "_" eq.triple "_ " (mod n) : ZZ times ZZ -> "Propo",
    (a,b) |-> n | (a - b)
  $
]

#proposition[
  给定正整数 $n$，$"_" eq.triple "_ " (mod n)$ 是等价关系.
]

#definition[
  设 $n in NN_+$. 定义函数
  $
    ["_"]_n : ZZ -> ZZ slash ("_" eq.triple "_ " (mod n)), a |-> [a]_n := "等价类" {b in ZZ | b eq.triple a" "(mod n)}.
  $
  定义集合
  $
    ZZ slash n ZZ := ZZ slash ("_" eq.triple "_ " (mod n)) =
    {[0]_n, ... , [n-1]_n}.
  $
  定义 $ZZ slash n ZZ$ 上的加法
  $
    + : ZZ slash n ZZ times ZZ slash n ZZ -> ZZ slash n ZZ, ([a]_n, [b]_n) |-> [a]_n +[b]_n := [a + b]_n.
  $
]

#proposition[
  $forall a,b in ZZ". "
  a eq.triple a' (mod n) and b eq.triple b' (mod n)
  => (a + b) eq.triple (a + b)' (mod n)$.
]

#proposition[
  $forall a,b in ZZ". "
  a eq.triple b" "(mod n) <=> [a]_n = [b]_n$.
]
#corollary[
  $forall a, a', b, b' in ZZ". "
  [a]_n = [a']_n and [b]_n = [b']_n
  => [a]_n + [b]_n = [a']_n + [b']_n$.
]

#definition[
  *模运算*

  定义二元函数
  $
    "_" mod "_" : ZZ times ZZ_+ -> ZZ,
    (a, n) |-> a mod n := r,
  $
  其中 $r$ 是唯一使得
  $
    [r]_(n) = [a]_(n) and r in {0, ... , n - 1}
  $
  成立的整数.
]

#proposition[
  $forall n in ZZ_+". " 0 mod n = 0$
]

#definition[
  *欧几里得算法*（求*最高公因子*（*highest common factor*））
  
  ```
  let hcf(a : Int, b : Int_pos) :=
    if a mod b = 0
      b
    else
      hcf(b, a mod b)
  ```
]

#proposition[
  $forall b in ZZ_+". " "hcf" (0, b) = b$
]

#theorem[
  $
    forall a in ZZ, b in ZZ_+" "exists x,y in ZZ". "
    x a + y b = "hcf" (a, b)
  $
]

== *线性丢番图方程*

#corollary[
  Bézout 定理

  $forall a, c in ZZ, b in ZZ_+". "
    (exists x,y in ZZ". " a x + b y = c) <=>
    "hcf" (a, b) | c$
]

#lemma[
  $forall p in PP, a,b in ZZ". " p | a b => p | a or p | b$
]

#theorem[
  *算术基本定理*

  $
    forall n in ZZ_(>=2)". n 能唯一地表示成质数的乘积（不考虑顺序）."
  $
]

#proposition[
  $forall m in ZZ, n in ZZ_+". " "hcf" (m, n) dot.op "lcm" (m, n) = |m n|$，其中 $op("lcm")$ 是最低公倍数（lowest common multiple）.
]

#pagebreak()

= *初探范畴论*

== *范畴与态射*

#definition[
  一个*范畴* $cal(C)$ 系指以下资料：

  1. 集合 $op("Obj")(cal(C))$，其元素称作 $cal(C)$ 的*对象*；
  2. 对于每对对象 A 和 B，给定一个集合 $A -> B$，其元素称作 $cal(C)$ 的*态射*，满足：
  
  $
  forall A,B,C,D in op("Obj")(cal(C))". "
  not(A = C and B = D) =>
  (A -> B) sect (C -> D) = emptyset"；"
  $

  3. 对于每个对象 $A$，给定一个态射 $1_A : A -> A$，称为 $A$ 到自身的*恒等态射*；
  
  4. 对于任意 $A,B,C in op("Obj")(cal(C))$，给定态射间的*合成映射*
  $
    (A -> B) times (B -> C) -> (A -> C), (f,g) |-> g compose f"，"
  $
  满足：
  
  $
    "(i)" forall f : A -> B, g : B -> C, h : C -> D". "
    (h compose g) compose f = h compose (g compose f)"，"
  $
  $
    "(ii)" forall A,B in op("Obj")(cal(C)), f : A -> B". "
    f compose 1_A = f = 1_B compose f.
  $
]

#definition[
  对于任意范畴 $cal(C)$，其*反范畴* $cal(C)^(op)$ 定义如下：

  $1." "op("Obj")(cal(C)^(op)) := op("Obj")(cal(C))$；

  $2." "forall A,B in op("Obj")(cal(C)^(op))". "
  A -> B := (B -> A)_(cal(C))$；

  $3." "forall f : A -> B, g : B -> C". "
  g compose f := (f compose g)_(cal(C))$.
]

#definition[
  称 $cal(C)'$ 是 $cal(C)$ 的*子范畴*，如果

  $1." "op("Obj") (cal(C)') subset op("Obj")(cal(C))$；
  
  $2." "forall A,B in op("Obj")(cal(C)')". "
  A -> B subset (A -> B)_(cal(C))$；

  $3." "forall f : A -> B, g : B -> C". "
  g compose f := (g compose f)_(cal(C))$；
  
  $4.$ 恒等态射同 $cal(C)$.

  如果 $forall A,B in op("Obj")(cal(C)')". "
  A -> B = (A -> B)_(cal(C))$，则称 $cal(C)'$ 是
  $cal(C)$ 的*全子范畴*.
]

#definition[
  对于态射 $f : A -> B$，若存在 $g : B -> A$ 使得
  $g compose f = 1_A$, $f compose g = 1_B$，则称
  $f$ 是*同构*（或称可逆，写作 $f : A tilde(->) B$），而
  $g$ 则称为 $f$ 的*逆*.
]

#proposition[
  态射 $f$ 有左逆 $g_1$ 和右逆 $g_2$ $=>$
  $f$ 有唯一的逆 $f^(-1) = g_1 = g_2$.
]

#proposition[
  每个恒等态射都是同构，且是自己的逆.
]

#proposition[
  $f$ 是同构 $=>$ $f^(-1) "是同构" and (f^(-1))^(-1) = f$.
]

#proposition[
  $f : A -> B, g : B -> A$ 是两个同构 $=>$
  $g compose f "是同构" and (g compose f)^(-1) = f^(-1) compose g^(-1)$
]

#definition[
  若一个范畴 $cal(C)$ 中的所有态射都可逆，则称之为*群胚*.
]

#definition[
  设 $A, B$ 是范畴 $cal(C)$ 中的对象，$f : A -> B$ 为态射.

  1. $f$ 是*单态射*，$:<=>$
    $forall X in cal(C), g, h : X -> A". "
    g != h => f compose g != f compose h$（即满足左消去律）；
  2. $f$ 是*满态射*，$:<=>$
    $forall X in cal(C), g, h : B -> X". "
    g != h => g compose f != h compose f$（即满足右消去律）.
]

#proposition[
  $f$ 左（右）可逆 $=>$ $f$ 是单（满）态射.
]

#proposition[
  单（满）态射的合成是单（满）态射.
]

== *泛性质*

#definition[
  范畴 $cal(C)$ 中的对象 $A$ 称为*始对象*，如果对所有对象 $X$，集合 $A -> X$ 是单点集.
  类似的，称 $A$ 为*终对象*，如果对所有对象 $X$，集合 $X -> A$ 是单点集.
  若 $A$ 是始对象或终对象，则称之为*端对象*.
  若 $A$ 既是始对象又是终对象，则称之为*零对象*.
]

#proposition[
  设 $A, A'$ 为 $cal(C)$ 的始对象，则存在唯一的同构 $A tilde(->) A'$.
  同样的性质对终对象也成立.
]

#proposition[
  设 $A$ 为 $cal(C)$ 的始对象，$B in cal(C)$. 则
  $A tilde.eq B$ $<=>$ $B$ 是 $cal(C)$ 的始对象.
  同样的性质对终对象也成立.
]

#definition[
  设 $cal(C)$ 中有零对象，记作 $0$. 对任意 $X,Y in cal(C)$ 定义*零态射*
  $0 : X -> Y$ 为 $X -> 0 -> Y$ 的合成
]

#proposition[
  零态射从左右合成任何态射仍是零态射.
]

#proposition[
  零态射的定义无关零对象的选取：若 $0, 0'$ 都是零对象，则出入
  $0, 0'$ 的箭头都是唯一的，即下图交换
  #align(
    center,
    commutative-diagram(
      node((1, 0), $X$),
      node((0, 1), $0$),
      node((2, 1), $0'$),
      node((1, 2), $Y$),
      arr((1, 0), (0, 1), ""),
      arr((1, 0), (2, 1), ""),
      arr((0, 1), (2, 1), "", curve: 15deg),
      arr((2, 1), (0, 1), "", curve: 15deg),
      arr((0, 1), (1, 2), ""),
      arr((2, 1), (1, 2), ""),
    )
  )
]

#proposition[
  $emptyset$ 是 $bold("Set")$ 的唯一的始对象.
]

#definition[
  设 $cal(C)$ 是一个范畴，$*$ 是 $cal(C)$ 的终对象.

  定义  *$cal(C)^*$*：
  
  $"Obj"(cal(C)^*) := 
  {f : * -> X | X in cal(C)}$，

  $forall f : * -> X, g : * ->Y". "
  f -> g := {sigma : X -> Y | sigma compose f = g}$.

  $cal(C)^*$ 的对象称为*有点对象*.
]

#definition[
  一个构造满足一个*泛性质* $:<=>$
  它能被视为一个范畴的端对象.
]

#definition[
  设 $op(~)$ 是集合 $A$ 上的一个等价关系.
  
  定义 *$bold("Set")slash ~$*：

  $op("Obj")(bold("Set")slash ~) := 
  {phi : A -> X |
  X in op("Obj")(bold("Set")), forall a,b in A". " a op(~) b => phi(a) = phi(b)}$，

  $forall phi_1 : A -> X_1, phi_2 : A ->X_2". "
  phi_1 -> phi_2 :=
  {sigma : X_1 -> X_2 | sigma compose phi_1 = phi_2}$.
]

#proposition[
  $pi : A -> A slash ~, x |-> [x]_~$
  是 $bold("Set")slash ~$ 的始对象，如下图
  #align(
    center,
    commutative-diagram(
      node((1, 0), $A$),
      node((0, 1), $A slash ~$),
      node((2, 1), $X$),
      arr((1, 0), (0, 1), $pi$),
      arr((1, 0), (2, 1), $phi$, label-pos: right),
      arr((0, 1), (2, 1), $exists! tilde(phi)$, "dashed"),
    )
  )
]

#definition[
  设 $A, B in cal(C)$.
  $A$ 和 $B$ 的*积* $A times B$（若存在则）定义如下
  #align(
    center,
    commutative-diagram(
      node((0, 1), $X$),
      node((1, 0), $A$),
      node((1, 1), $A times B$),
      node((1, 2), $B$),
      arr((0, 1), (1, 0), $f_A$, label-pos: right),
      arr((0, 1), (1, 2), $f_B$),
      arr((1, 1), (1, 0), $pi_A$),
      arr((1, 1), (1, 2), $pi_B$, label-pos: right),
      arr((0, 1), (1, 1),
        text(size: 0.7em)[$f_A times f_B$],
        "dashed"),
    )
  )
]

#definition[
  *余积*
  #align(
    center,
    commutative-diagram(
      node((0, 1), $X$),
      node((1, 0), $A$),
      node((1, 1), $A union.sq B$),
      node((1, 2), $B$),
      arr((1, 0), (0, 1), $f_A$),
      arr((1, 2), (0, 1), $f_B$, label-pos: right),
      arr((1, 0), (1, 1), $i_A$, label-pos: right),
      arr((1, 2), (1, 1), $i_B$),
      arr((1, 1), (0, 1),
        text(size: 0.7em)[$f_A union.sq f_B$],
        label-pos: right, "dashed"),
    )
  )
]

#definition[
  *积*
  #align(
    center,
    commutative-diagram(
      node((0, 0), $X$),
      node((2, 0), $ product_(i : I) A_i $),
      node((1, 1), $A_(i_1)$),
      node((1, 2), $A_(i_2)$),
      node((1, 3), $...$),
      arr((0, 0), (1, 1),
        text(size: 0.9em)[$f_(i_1)$]),
      arr((0, 0), (1, 2),
        text(size: 0.9em)[$f_(i_2)"                ..."$]),
      arr((2, 0), (1, 1),
        text(size: 0.9em)[$pi_(i_1)$],
        label-pos: right),
      arr((2, 0), (1, 2),
        text(size: 0.9em)[$pi_(i_2)"                ..."$],
        label-pos: right),
      arr((0, 0), (2, 0),
        label-pos: right,
        text(size: 0.9em)[$ product_(i : I) f_i $],
        "dashed"),
    )
  )
]

#definition[
  *拉回*
  #align(
    center,
    commutative-diagram(
      node((0, 0), $X$),
      node((1, 1), $A times_C B$),
      node((2, 1), $A$),
      node((1, 2), $B$),
      node((2, 2), $C$),
      arr((2, 1), (2, 2), $alpha$, label-pos: right),
      arr((1, 2), (2, 2), $beta$),
      arr((1, 1), (2, 1), $p_alpha$, label-pos: right),
      arr((1, 1), (1, 2), $p_beta$),
      arr((0, 0), (2, 1), $f_alpha$,
        label-pos: right, curve: -15deg),
      arr((0, 0), (1, 2), $f_beta$, curve: 15deg),
      arr((0, 0), (1, 1),
        text(size: 0.8em)[$f_alpha times_C f_beta$],
        "dashed")
    )
  )
]

#proposition[
  设 $cal(C)$ 是一个范畴，$G times G$ 和 $H times H$ 是 $cal(C)$ 中的积. 则有
  #align(
    center,
    commutative-diagram(
      node((0,0), $G$),
      node((1,0), $G times G$),
      node((2,0), $G$),
      node((0,1), $H$),
      node((1,1), $H times H$),
      node((2,1), $H$),
      arr((0,0), (0,1), $phi$),
      arr((2,0), (2,1), $phi$, label-pos: right),
      arr((1,0), (0,0), $pi_G$),
      arr((1,0), (2,0), $pi_G$, label-pos: right),
      arr((1,1), (0,1), $pi_G$, label-pos: right),
      arr((1,1), (2,1), $pi_G$),
      arr((1,0), (0,1), $phi compose pi_G$, curve: 15deg),
      arr((1,0), (2,1), $phi compose pi_G$,
        label-pos: right, curve: -15deg),
      arr((1,0), (1,1), $exists! phi times phi$, "dashed"),
    )
  )
]

#proposition[
  设 $cal(C)$ 是一个范畴，$G times G, H times H, K times K$ 是 $cal(C)$ 中的积，且有态射 $G ->^phi H ->^psi K$.
  则 $(psi compose phi) times (psi compose phi) =
  (psi times psi) compose (phi times phi)$.
]

#pagebreak()

= *初探群论*

== *群*

#let joke = thm-base(type: "笑话", color: fuchsia)

#joke[
  一个*群*是一个只有一个对象的群胚.
]

#definition[
  设 $G$ 是一个非空集合，$dot : G times G -> G$.

  $(G, dot)$ 是一个*群* $:<=>$ 
  $
    1. "结合律:" forall g,h,k in G". " (g dot h) dot k = g dot (h dot k);
  $$
    2. "存在幺元:" exists e in G" "forall g in G". " g dot e = g = e dot g;
  $$
    3. "所有元素皆可逆:" forall g in G" "exists h in G". " g dot h = e = h dot g.
  $
]

#proposition[
  一个群的幺元是唯一的.
]

#proposition[
  一个元素的逆是唯一的.
]

#proposition[
  消去律：$forall g,h,k in G". "
  g != h => g dot k != h dot k and
  k dot g != k dot h$.
]

#proposition[
  $forall g,h in G". " (g dot h)^(-1) = h^(-1) dot g^(-1)$.
]

#definition[
  一个群是*交换*的 $:<=>$ $forall g,h in G". " g dot h = h dot g$
]

== *阶*

#definition[
  群 $G$ 的基数 $|G|$ 称为它的*阶*.
]

#example[
  #grid(
    columns: (auto, auto, auto, auto, auto),
    gutter: 5pt,
    table(
      columns: (auto, auto),
      align: horizon,
      [*$dot$*], [*$e$*],
      [*$e$*], [$e$],
    ),
    table(
      columns: (auto, auto, auto),
      align: horizon,
      [*$dot$*], [*$e$*], [*$a$*],
      [*$e$*], [$e$], [$a$],
      [*$a$*], [$a$], [$e$],
    ),
    table(
      columns: (auto, auto, auto, auto),
      align: horizon,
      [*$dot$*], [*$e$*], [*$a$*], [*$b$*],
      [*$e$*], [$e$], [$a$], [$b$],
      [*$a$*], [$a$], [$b$], [$e$],
      [*$b$*], [$b$], [$e$], [$a$],
    ),
    table(
      columns: (auto, auto, auto, auto,auto),
      align: horizon,
      [*$dot$*], [*$e$*], [*$a$*], [*$b$*], [*$c$*],
      [*$e$*], [$e$], [$a$], [$b$], [$c$],
      [*$a$*], [$a$], [$e$], [$c$], [$b$],
      [*$b$*], [$b$], [$c$], [$e$], [$a$],
      [*$c$*], [$c$], [$b$], [$a$], [$e$],
    ),
    table(
      columns: (auto, auto, auto, auto,auto),
      align: horizon,
      [*$dot$*], [*$e$*], [*$a$*], [*$b$*], [*$c$*],
      [*$e$*], [$e$], [$a$], [$b$], [$c$],
      [*$a$*], [$a$], [$b$], [$c$], [$e$],
      [*$b$*], [$b$], [$c$], [$e$], [$a$],
      [*$c$*], [$c$], [$e$], [$a$], [$b$],
    ),
  )
]

#proposition[
  所有小于等于 4 阶的群都是交换的.
]

#definition[
  群 $G$ 的元素 $g$ *有有限阶* $:<=>$ $exists n in NN". " g^n = e$.

  在此情況下，$g$ 的*阶* $|g| := min{n in NN_+ | g^n = e}$.

  若 $g$ 沒有有限阶，则记为 $|g| = oo$.
]

#proposition[
  如果 $g^n = e$，则 $|g|$ 是 $n$ 的一个因子（即 $n$ 是 $|g|$ 的一个倍数）.
]

#proposition[
  $forall g in G". " |g| <= |G|$.
]

#proposition[
  $g in G$ 有有限阶 $=>$
  $forall m in NN". " g^m$ 有有限阶
  $and |g^m| = (op("lcm")(m, |g|)) / m = |g| / (op("hcf")(m, |g|))$.
]

#proposition[
  $g dot h = h dot g =>
  |g dot h| "整除" op("lcm")(|g|, |h|)$.
]

#proposition[
  $(forall g in G". " |g| = 2) => G "是交换的."$
]

#proposition[
  $forall g,h in G". " |g dot h| = |h dot g|$.
]

#proposition[
  $g dot h = h dot g and |g|" 和" |h| "互质" =>
  |g dot h| = |g| dot |h|$.
]

#proposition[
  设 $G$ 是一个交换群，$g in G$ 有有限阶且
  $forall h in G". " h "有有限阶" => |h| <= |g|$. 则

  $forall h in G". " h "有有限阶" => |h| "整除" |g|$.
]

== *群的例子*

=== *对称群*

#definition[
  设 $A in bold("Set")$. $A$ 的*对称群* $S_A$ 定义为群 $"Aut"_bold("Set") (A)$.
]

#proposition[
  $|S_n| = n!$.
]

#proposition[
  $|S_0| = |S_1| = 1$.
]

#proposition[
  $forall n >= 3". " S_n$ 是非交换的.
]

#proposition[
  $forall d in {0, ... , n}" "exists sigma in S_n". " |sigma| = d.$
]

#proposition[
  $forall n in NN_+" "exists sigma in S_NN". " |sigma| = n.$
]

=== *二面体群*

#definition[
  一个*对称*是一个保持结构的变换.
]

#definition[
  一个正 $n$ 边形有 $2n$ 个不同的对称：$n$ 个旋转对称和 $n$ 个反射对称. 相应的旋转和反射组成了*二面体群* $D_(2n)$.
]

=== *循环群*

#definition[
  一个群 $G$ 是*循环*的 $:<=>$
  $exists a in G" "forall b in G" "exists m in ZZ". " b "可以表示为" a^m$，即 $G = {a^m | m in ZZ}$.
  其中 $a$ 被称为 $G$ 的一个*生成元*.
]

#proposition[
  设 $G$ 是 $n$ 阶循环群，$a$ 是 $G$ 的一个生成元. 则
  $G = {a^0 = e, a, a^2, ... , a^(n-1)}$.
]

#definition[
  *无限循环群*
  $
    angle.l a angle.r :=
    {..., a^(-2), a^(-1), a^0 = e, a, a^2, ...}.
  $
]

#proposition[
  设 $G$ 是一个 $n$ 阶群. 则
  $G "是循环的" <=> exists g in G". " |g| = n$.
]

#proposition[
  $ZZ$ 和 $ZZ slash n ZZ$ 都是循环群，它们的生成元分別是 $1$ 和 $[1]_n$.
]

#proposition[
  $forall m in ZZ, n in ZZ_+". " |[m]_n| = n / (op("hcf")(m, n))$.
]

#corollary[
  $forall m in ZZ, n in ZZ_+". "
  [m]_n"生成" ZZ slash n ZZ <=> op("hcf")(m, n) = 1$.
]

#definition[
  *整数模 $n$ 乘法群*
  
  $
    (ZZ slash n ZZ)^* :=
    {[m]_n in ZZ slash n ZZ | [m]_n"生成" ZZ slash n ZZ}"，"
  $$
    dot : (ZZ slash n ZZ)^* times (ZZ slash n ZZ)^* -> (ZZ slash n ZZ)^*, ([a]_n, [b]_n) |-> [a]_n dot [b]_n := ["ab"]_n.
  $
]

#lemma[
  $forall a, a', b, b' in ZZ". "
  [a]_n = [a']_n and [b]_n = [b']_n =>
  [a]_n dot [b]_n = [a']_n dot [b']_n.$
]

#proposition[
  $((ZZ slash n ZZ)^*, dot)$ 是群.
]

== *群范畴 $bold("Grp")$*

#definition[
  集合函数 $phi : G -> H$ 是一个群*同态* $:<=>$

  图
  #align(
    center,
    commutative-diagram(
      node((0,0), $G times G$),
      node((1,0), $G$),
      node((0,1), $H times H$),
      node((1,1), $H$),
      arr((0,0), (1,0), $dot_G$, label-pos: right),
      arr((0,1), (1,1), $dot_H$),
      arr((1,0), (1,1), $phi$, label-pos: right),
      arr((0,0), (0,1), $phi times phi$),
    )
  )
  交换，即 $phi(a dot b) = phi(a) dot phi(b)$.
]

#definition[
  *群范畴* $bold("Grp")$

  $
    op("Obj")(bold("Grp")) := {"所有群"}"，"
  $$
    forall G, H in op("Obj")(bold("Grp"))". "
    G -> H := {"从 " G "到 " H "的群同态"}.
  $
]

#definition[
  设 $G in bold("Grp")$. 定义函数
  *$iota_G$* $: G -> G,
  g |-> g^(-1)$.
]

#proposition[
  设 $phi : G -> H$ 是一个群同态. 则

  $1." "phi(e_G) = e_H$；

  $2.$ 图
  #align(
    center,
    commutative-diagram(
      node((0,0), $G$),
      node((0,1), $H$),
      node((1,0), $G$),
      node((1,1), $H$),
      arr((0,0), (0,1), $phi$),
      arr((1,0), (1,1), $phi$, label-pos: right),
      arr((0,0), (1,0), $iota_G$, label-pos: right),
      arr((0,1), (1,1), $iota_H$),
    )
  )
  交换.
]

#proposition[
  平凡群 ${e}$ 是 $bold("Grp")$ 的零对象.
]

#definition[
  给定群 $G$ 和 $H$，它们的*直积* $G times H$ 系如下资料：

  1. 下层集合：集合 $G$ 和 $H$ 的积 $G times H$；
  2. 二元运算：$dot : (G times H) times (G times H) -> G times H,
  (g_1, h_1) dot (g_2, h_2) := (g_1 g_2, h_1 h_2)$.
]

#proposition[
  一个直积是一个群，且自然投影
  #align(
    center,
    commutative-diagram(
      node((0,1), $G times H$),
      node((0,0), $G$),
      node((0,2), $H$),
      arr((0,1), (0,0), $pi_G$, label-pos: right),
      arr((0,1), (0,2), $pi_H$),
    )
  )
  是群同态.
]

#proposition[
  群 $G$ 和 $H$ 的直积 $G times H$ 是范畴 $bold("Grp")$ 中的积.
]

== *交换群范畴 $bold("Ab")$*

#definition[
  *交换群范畴* $bold("Ab")$

  $
    op("Obj")(bold("Ab")) := {G in op("Obj")(bold("Grp")) | G "是交换的"}"，"
  $$
    forall G, H in op("Obj")(bold("Ab")), G -> H := (G -> H)_bold("Grp").
  $
]

#proposition[
  平凡群是 $bold("Ab")$ 的零对象.
]

#proposition[
  群 $G$ 和 $H$ 的直积 $G times H$ 同时是范畴 $bold("Ab")$ 中的积和余积.
]

#definition[
  作为余积时，群 $G$ 和 $H$ 的直积 $G times H$ 被称为它们的*直和*，并记为 $G plus.circle H$，如下图所示
  #align(
    center,
    commutative-diagram(
      node((0, 1), $X$),
      node((1, 0), $G$),
      node((1, 1), $G plus.circle H$),
      node((1, 2), $H$),
      arr((1, 0), (0, 1), $f_G$),
      arr((1, 2), (0, 1), $f_H$, label-pos: right),
      arr((1, 0), (1, 1), $i_G$, label-pos: right),
      arr((1, 2), (1, 1), $i_H$),
      arr((1, 1), (0, 1),
        text(size: 0.7em)[$f_G plus.circle f_H$],
        label-pos: right, "dashed"),
    )
  )
  其中，
  $
    i_G : G -> G plus.circle H, g |-> (g, e_H),
  $$
    i_H : H -> G plus.circle H, h |-> (e_G, h).
  $
]

== *群同态*

=== *例子*

#definition[
  设 $G$ 和 $H$ 是群. 定义*平凡态射* $sigma : G -> H, g |-> e_H$.
  显然，平凡态射一定存在.
]

#definition[
  设 $cal(C)$ 是一个范畴，$A in cal(C)$.
  群 $G$ 在 $A$ 上的一个 *作用* 是一个群同态
  $sigma : G -> op("Aut"_C)(A)$.
]

#example[
  设 $a,b,c$ 是某个正三角形的三个顶点. 我们知道 $S_3 = op("Aut"_bold("Set")){a,b,c}$，且有群同态 $sigma : D_(2 dot 3) -> S_3$.
  我们称“群 $D_(2 dot 3)$ 作用于正三角形的顶点”.
]

#definition[
  设 $G$ 是一个群，$g$ 是 $G$ 的一个元素.
  定义*指数映射* $epsilon_g : ZZ -> G, m |-> g^m$.
]

#proposition[
  $epsilon_g (a + b) = epsilon_g (a) dot epsilon_g (b)$，也就是说，指数映射 $epsilon_g$ 是一个群同态.
]

#proposition[
  设 $a in ZZ$.
  则指数映射
  $epsilon_a : ZZ -> angle.l a angle.r, m |-> a^m$
  是一个群同构.
]

#definition[
  给定正整数 $n$，定义群同态
  $
    pi_n : ZZ -> ZZ slash n ZZ, a |->
    epsilon_([1]_n) (a) = a [1]_n = [a]_n.
  $
]

#proposition[
  $m | n =>$
  存在一个群同态 $pi_m^n : ZZ slash n ZZ -> ZZ slash m ZZ$
  使得图
  #align(
    center,
    commutative-diagram(
      node((0,0), $ZZ$),
      node((1,0), $ZZ slash n ZZ$),
      node((1,1), $ZZ slash m ZZ$),
      arr((0,0), (1,0), $pi_n$, label-pos: right),
      arr((0,0), (1,1), $pi_m$),
      arr((1,0), (1,1), $pi_m^n$, label-pos: right),
    )
  )
  交换，即 $pi_m^n ([a]_n) = [a]_m$.
]

=== *同态与阶*

#proposition[
  设 $phi : G -> H$ 为一个群同态，$g in G$ 是一个有有限阶的元素.
  则 $|phi(g)|$ 整除 $|g|$.
]

=== *群同构*

#definition[
  一个*群同构* $phi : G -> H$ 是 $bold("Grp")$ 中的一个同构.
]

#proposition[
  设 $phi : G -> H$ 为一个群同态. 则
  $phi "是一个群同构" <=> phi "是一个双射"$.
]

#proposition[
  设 $phi : G -> H$ 是一个群同构. 则

  $1." "forall g in G". " |phi(g)| = |g|$；

  $2." "G "是交换的" <=> H "是交换的"$.
]

#proposition[
  $"群" (ZZ, +) tilde.eq.not "群" (QQ, +).$
]

#proposition[
  函数 $exp : (RR, +) -> (RR_(>0), dot), x |-> e^x$ 是群同构.
]

#proposition[
  $"群" (QQ, +) tilde.eq.not "群" (QQ_(>0), dot).$
]

=== *交换群的同态*

#proposition[
  设 $G$ 和 $H$ 是两个交换群，定义二元函数
  $
    + : (G -> H)_bold("Ab") times (G -> H)_bold("Ab") -> (G -> H)_(bold("Set")),
  $$
    (phi, psi) |-> phi + psi,
    (phi + psi)(g) := phi(g) + psi(g).
  $
  则 $(G -> H)_bold("Ab")$ 对 $+$ 封闭，且 $((G -> H)_bold("Ab"), +) in bold("Ab")$.
]

#proposition[
  设 $A$ 是一个集合，$H$ 是一个交换群. 则
  $((A -> H)_bold("Set"), +) in bold("Ab")$.
]

#proposition[
  设 $G$ 是一个群. 则

  $1. "函数" g |-> g^(-1) : G -> G "是一个群同构" <=>
  G "是交换的；"$

  $2. "函数" g |-> g^2 : G -> G "是一个群同态" <=>
  G "是交换的."$
]

== *自由群*

=== *泛性质*

#definition[
  *自由群*

  给定集合 $S$，定义范畴 *$cal(F)_S$*：
  $
    op("Obj")(cal(F)_S) :=
    {iota : (S -> G)_bold("Set") | G in op("Obj")(bold("Grp"))}，
  $$
    iota_1 -> iota_2 :=
    {phi : (op("codom") iota_1 -> op("codom") iota_2)_(bold("Grp")) | phi compose iota_1 = iota_2}.
  $

  #align(
    center,
    commutative-diagram(
      node((0,0), $S$),
      node((0,1), $op("codom") iota_1$),
      node((1,1), $op("codom") iota_2$),
      arr((0,0), (0,1), $iota_1$),
      arr((0,0), (1,1), $iota_2$, label-pos: right),
      arr((0,1), (1,1), $phi$),
    )
  )

  集合 $S$ 上的*自由群*定义为 $cal(F)_S$ 中的始对象（如果存在的话；后面我们会证明它一定存在）
  #align(
    center,
    commutative-diagram(
      node((0,0), $S$),
      node((0,1), $F(S)$),
      node((1,1), $G$),
      arr((0,0), (0,1), $iota$),
      arr((0,0), (1,1), $f$, label-pos: right),
      arr((0,1), (1,1), $phi$, "dashed"),
    )
  )
]

#proposition[
  给定集合 $S$ 和平凡群 ${e}$，则 $({e}, s |-> e : S -> {e})$ 是范畴 $cal(F)_S$ 的终对象.
]

=== *具体构造*

#definition[
  对于任何集合 $S$，如果我们把它的元素当作*字符*，则可称其为一个*字符集*.
]

#definition[
  对于任何字符 $a$，定义其*逆字符*为字符 $a^(-1)$.

  一个字符集 $S$ 的所有字符的逆字符的集合记为 $S^(-1)$.
]

#definition[
  一个字符集 $S$ 上的所有*字符串*的集合定义如下

  $1.$ 如果 $S = emptyset$，则 $S^* := {"空字符串"}$；

  $2.$ 如果 $S$ 非空，则 $S^* := {"空字符串"} union {a_1 ... a_n | n in NN_+, a_i in S}$.
]

#convention[
  $1.$ 对于任何字符 $a$，我们可以把 $(a^(-1))^(-1)$ 化简为 $a$；

  $2.$ 对于任何字符串 $x$，其中形如 $a a^(-1)$ 或 $a^(-1) a$ 的部分都能化简为空字符串；

  $3.$ 我们不区分字符以及字符串的化简前后的形式.
]

#definition[
  *自由群*

  设 $S$ 是一个字符集，$T = S union S^(-1)$.

  定义 $T^*$ 上的乘法：
  $
    dot : T^* times T^* -> T^*, (x, y) |-> x y，
  $
  即字符串连接.

  显然，$(T^*, dot)$ 构成一个群结构（乘法符合结合律；有幺元，即空字符串；每个字符串都有逆元），称该群为集合 $S$ 生成的*自由群*.
]

#proposition[
  设 $S$ 是一个集合，$F_S$ 是它生成的自由群，函数 $iota : S -> F_S, \'a\' |-> \"a\"$. 则 $iota$ 满足 $S$ 上的自由群的泛性质.
]

#example[
  二元集 ${x, y}$ 生成的自由群的 Cayley 图
  #align(center, image("cayley-freegroup-twopoints.png", width: 70%))
]

=== *自由交换群*

#definition[
  *自由交换群*

  给定集合 $S$，定义范畴 *$cal(F)_S^bold("Ab")$*：
  $
    op("Obj")(cal(F)_S^bold("Ab")) :=
    {iota : (S -> G)_bold("Set") | G in op("Obj")(bold("Ab"))}，
  $$
    iota_1 -> iota_2 :=
    {phi : (op("codom") iota_1 -> op("codom") iota_2)_(bold("Ab")) | phi compose iota_1 = iota_2}.
  $

  #align(
    center,
    commutative-diagram(
      node((0,0), $S$),
      node((0,1), $op("codom") iota_1$),
      node((1,1), $op("codom") iota_2$),
      arr((0,0), (0,1), $iota_1$),
      arr((0,0), (1,1), $iota_2$, label-pos: right),
      arr((0,1), (1,1), $phi$),
    )
  )

  集合 $S$ 上的*自由交换群*定义为 $cal(F)_S^bold("Ab")$ 中的始对象（如果存在的话；后面我们会证明它一定存在）.
  #align(
    center,
    commutative-diagram(
      node((0,0), $S$),
      node((0,1), $F^bold("Ab") (S)$),
      node((1,1), $G$),
      arr((0,0), (0,1), $iota$),
      arr((0,0), (1,1), $f$, label-pos: right),
      arr((0,1), (1,1), $phi$, "dashed"),
    )
  )
]

#definition[
  *$ZZ^(plus.circle n)$*

  设 $n in NN$. 定义 *$ZZ^(plus.circle n)$*

  $1.$ *$ZZ^(plus.circle 0)$* $:= {"空元组"}$，令其为平凡群；

  $2.$ 如果 $n > 0$，则 *$ZZ^(plus.circle n)$* $:= underbrace(ZZ plus.circle ... plus.circle ZZ, "n 次")$，并定义其上二元运算 $dot : ZZ^(plus.circle n) times ZZ^(plus.circle n) -> ZZ^(plus.circle n), (x_1, ... , x_n) dot (y_1, ... , y_n) := (x_1 dot y_1, ... , x_n dot y_n)$，这也构成一个群.
]

#proposition[
  $1.$ 设函数 $iota : emptyset -> ZZ^(plus.circle 0)$. 则 *$iota$* 满足 $emptyset$ 上的自由交换群的泛性质.

  $2.$ 设 $n in NN_+$，$S = {1, ... , n}$，函数 $iota : S -> ZZ^(plus.circle n), i |-> (0, ... , 0, underbrace(1, "第 i 位"), 0, ... , 0)$. 则 *$iota$* 满足 $S$ 上的自由交换群的泛性质.
]

#definition[
  $bold(H^(plus.circle S))$

  设 $S$ 是一个集合，$H$ 是一个交换群.
  $
    H^(plus.circle S) :=
    {alpha : (S -> H)_bold("Set") | {s in S | op(alpha) (s) != e_H} "是有限集"}
  $

  显然 *$(H^(plus.circle S), +)$* 是交换群.
]

#proposition[
  设 $S$ 是一个集合，函数 $iota : S -> ZZ^(plus.circle S), iota(s) := (x in S) |->
  cases(
    1"," x = s,
    0"," x != s
  )$ .
  则 *$iota$* 满足 $S$ 上的自由交换群的泛性质.
]

== *子群*

#definition[
  *子群*

  设 $(G, dot)$ 和 $(H, circle.filled.tiny)$ 是群，且它们的下层集合间有关系 $H subset G$.
  
  $(H, circle.filled.tiny)$ 是 $(G, dot)$ 的一个*子群* $:<=>$
  包含函数 $i : H arrow.r.hook G$ 是一个群同态.
]

#proposition[
  设 $(G, dot)$ 是一个群，$H$ 是 $G$ 的一个非空子集. 则 $(H, dot)$ 是 $(G, dot)$ 的一个子群 $<=> forall a, b in H". "a b^(-1) in H$.
]

#lemma[
  如果 ${H_alpha}_(alpha in A)$ 是群 $G$ 的一族子群，则 $sect.big_(alpha in A) H_alpha$ 是 $G$ 的一个子群.
]

#lemma[
  设 $phi : G -> G'$ 是一个群同态，$H'$ 是 $G'$ 的一个子群. 则 $phi^(-1) (H')$ 是 $G$ 的一个子群.
]

#definition[
  *核*

  群同态 $phi : G -> G'$ 的*核*定义为：
  
  $
    bold(op("ker") phi) := op(phi)^(-1) (e_(G')).
  $
]

#proposition[
  设 $phi : G -> G'$ 是一个群同态. 那么

  $1.$ $op("ker") phi$ 是 $G$ 的一个子群.
  
  $2.$ 对于 $G$ 的任何子群 $H$，$op(phi)(H)$ 是 $G'$ 的一个子群.
]

#import "@preview/fletcher:0.4.4" as fletcher: diagram, node, edge

#proposition[
  设 $phi : G -> G'$ 是一个群同态.
  定义一个范畴 $cal(C)$，$op("Obj")(cal(C)) := {alpha : (K -> G)_bold("Grp") | K in bold("Grp"), phi compose alpha = "平凡同态" op(0) : K -> G' ("即" op(alpha)(K) subset op("ker")phi)}$，$forall alpha : (K -> G)_bold("Grp"), beta : (L -> G)_bold("Grp")". " alpha -> beta := {gamma : (K -> L)_bold("Grp") | alpha = beta compose gamma}$. 则包含函数 $i : op("ker") phi -> G$ 是范畴 $cal(C)$ 的终对象，如下图

  #align(center, diagram(spacing: 2cm, {
    let (k, g, gt, ker) = ((-1,0), (0,0), (1,0), (0,1))
    node(k, $K$)
    node(g, $G$)
    node(gt, $G'$)
    node(ker, $op("ker") phi$)

    edge(k, g, $alpha$,label-side: right, "->")
    edge(g, gt, $phi$,label-side: right, "->")
    edge(k, gt, bend: +30deg, $0$, "->")
    edge(ker, g, $i$, "hook->")
    edge(k, ker, $exists ! macron(alpha)$, label-side: right, "-->")
  }))
]

#definition[
  *生成子群*

  第 $1$ 种定义：

  如果 $A$ 是群 $G$ 的一个子集，$i : A -> G$ 是包含映射，$iota$ 满足 $A$ 上的自由群的泛性质，那么我们有一个唯一的群同态 $phi : F(A) -> G$ 使得下图交换

  #align(center, diagram(spacing: 3cm, {
    let (a, fa, g) = ((0,0), (1,0), (1,1))
    node(a, $A$)
    node(fa, $F(A)$)
    node(g, $G$)

    edge(a, fa, $iota$, "->")
    edge(a, g, $i$, label-side: right, "->")
    edge(fa, g, $phi$, label-side: left, "-->")
  }))

  我们称 $op(phi)(F(A))$ 为*群 $G$ 中由子集 $A$ 生成的子群*，记为 *$angle.l A angle.r$*.

  第 $2$ 种定义：

  定义 $angle.l A angle.r$ 的元素为具有以下形式的对象：

  $
    a_1 a_2 ... a_3，
  $

  其中每个 $a_i$ 是 $A$ 中的元素，或 $A$ 中的元素的逆，或幺元.

  第 $3$ 种定义：

  $
    angle.l A angle.r := sect.big {G "的包含" A "子群"}.
  $
]

#proposition[
  交换群经过群同态输出的像是交换群.
]

#proposition[
  给定集合 $A$，定义范畴 *$cal(F)_A$*：
  $
    op("Obj")(cal(F)_A) :=
    {iota : (A -> G)_bold("Set") | G in op("Obj")(bold("Grp"))}，
  $$
    iota_1 -> iota_2 :=
    {phi : (op("codom") iota_1 -> op("codom") iota_2)_(bold("Grp")) | phi compose iota_1 = iota_2}.
  $

  #align(center, diagram(spacing: 3cm, {
    let (a, fa, g) = ((0,0), (1,0), (1,1))
    node(a, $A$)
    node(fa, $op("codom") iota_1$)
    node(g, $op("codom") iota_2$)

    edge(a, fa, $iota_1$, "->")
    edge(a, g, $iota_2$, label-side: right, "->")
    edge(fa, g, $phi$, label-side: left, "-->")
  }))

  定义它的子范畴 *$cal(F)_A^bold("Ab")$*：
  $
    op("Obj")(cal(F)_A^bold("Ab")) :=
    {iota : (A -> G)_bold("Set") | G in op("Obj")(bold("Ab"))}，
  $$
    iota_1 -> iota_2 :=
    {phi : (op("codom") iota_1 -> op("codom") iota_2)_(bold("Ab")) | phi compose iota_1 = iota_2}.
  $

  #align(center, diagram(spacing: 3cm, {
    let (a, fa, g) = ((0,0), (1,0), (1,1))
    node(a, $A$)
    node(fa, $op("codom") iota_1$)
    node(g, $op("codom") iota_2$)

    edge(a, fa, $iota_1$, "->")
    edge(a, g, $iota_2$, label-side: right, "->")
    edge(fa, g, $phi$, label-side: left, "-->")
  }))

  设 $iota_1$ 和 $iota_2$ 分别是 $cal(F)_A$ 和 $cal(F)_A^bold("Ab")$ 的始对象，且下图交换

  #align(center, diagram(spacing: 3cm, {
    let (a, fa, g) = ((0,0), (1,0), (1,1))
    node(a, $A$)
    node(fa, $F(A)$)
    node(g, $F^bold("Ab") (A)$)

    edge(a, fa, $iota_1$, "->")
    edge(a, g, $iota_2$, label-side: right, "->")
    edge(fa, g, $phi$, label-side: left, "-->")
  }))

  那么，$phi$ 是满射.
]
