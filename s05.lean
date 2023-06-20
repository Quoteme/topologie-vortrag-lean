import topology.basic
import topology.path_connected
import analysis.inner_product_space.basic
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

example : topological_space (ℝ×ℝ×ℝ) := by apply_instance 

example : @ is_simply_connected _ _ (1,0,0) S2 _ :=
begin
  unfold is_simply_connected,
  split,
  {
    unfold is_path_connected,
    use (1,0,0),
    split,
    {
      unfold S2,
      simp,
      -- zeige, dass ‖(1,0,0)‖ = 1 ist
      unfold norm,
      simp,
    },
    {
      intro y,
      intro hy,
      -- decompose y into y1, y2, y3
      -- cases y with y1 y23,
      -- cases y23 with y2 y3,
      -- let y := (y1,y2,y3),
      unfold joined_in,
      -- Wir möchten nun den Pfad von (1,0,0) nach y konstruieren.
      let f : path (1,0,0) y := {
        -- betrachte die Definition von `path` mit <kbd>ctrl</kbd>+<kbd>click</kbd> auf `path`
        -- wir brauchen also auf jeden fall:
        source' := by simp,
        target' := sorry,
        -- target' := _,
        -- außerdem steht dort `extends C(I, X)`, also brauchen wir noch:
        to_fun := λ t, (1,0,0),
        continuous_to_fun := by continuity,
      },
      use f,
      intro y',
      simp,
      unfold S2,
      simp,
      unfold norm,
      simp,
    }
  },
  {
    intro γ,
    intro hγ,
    unfold is_homotopic_to,
    let trivialPath : path (1,0,0) (1,0,0) := {
      source' := by simp,
      target' := by simp,
      to_fun := λ t, (1,0,0),
      continuous_to_fun := by continuity,
    },
    let f := (λ γ': path (1,0,0) (1,0,0), trivialPath),
    -- warum klappt es für f' aber nicht für f?
    let f' := (λ x, x),
    use f',
    split,
    {
      by continuity,
    },
    {
      unfold path.refl,
      sorry
    }
  }
end