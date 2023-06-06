import topology.basic
import topology.path_connected
import analysis.normed_space.basic
import data.set.basic
import algebraic_topology.fundamental_groupoid.simply_connected
import s01
import s02
import s03
import s04

/-
# Beweis der Theoreme

## $S^2$ ist einfach-zusammenhängend

Wir wollen zeigen, dass $S^2$ einfach-zusammenhängend ist.
Dazu zeigen wir, dass jede geschlossene Kurve in $S^2$ nullhomotop ist.
Sei $f: S^1 \to S^2$ eine geschlossene Kurve in $S^2$.
Wir definieren eine Homotopie $H: S^1 \times I \to S^2$ durch $H(x,t) = (1-t)f(x)$.
Diese ist stetig, da $f$ stetig ist. Außerdem ist $H(x,0) = f(x)$ 
und $H(x,1) = 0$ für alle $x \in S^1$. Somit ist $f$ nullhomotop
und $S^2$ einfach-zusammenhängend.
-/

def S2'' : Type := { x : ℝ × ℝ × ℝ  | ‖x‖ = 1 }

example : is_simply_connected S2 :=