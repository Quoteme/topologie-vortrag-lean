import topology.basic
import topology.path_connected
import topology.metric_space.basic
import analysis.inner_product_space.basic
import analysis.normed_space.basic
import data.set.basic
import algebraic_topology.fundamental_groupoid.simply_connected
import data.real.basic
import analysis.special_functions.trigonometric.basic
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

-- definiere ℝ×ℝ×ℝ als topologischen Raum
example : topological_space (ℝ×ℝ×ℝ) := by apply_instance 

-- definiere ℝ×ℝ×ℝ als metrischen Raum
instance : metric_space (ℝ×ℝ×ℝ) := by apply_instance

-- Zeige, dass die Norm ℝ×ℝ×ℝ → S2 stetig ist
-- lemma norm_continuous_on_S2 : continuous_on (norm : (ℝ × ℝ × ℝ) → ℝ) S2 :=
-- begin
--   rw continuous_on_iff_continuous_restrict,
--   apply continuous_norm.comp,
--   --apply continuous_subtype_val.continuous_on,
--   sorry
-- end

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
        source' := begin
          -- Hier möchten wir zeigen, dass (1,0,0) die Quelle von f ist.
          simp,
          unfold norm,
          simp,
        end,
        target' := begin
          simp,
          -- Hier möchten wir zeigen, dass wir auf jeden Fall am Ende unseres Pfades bei y ankommen.
          -- Wir haben zwei fälle: y = (1,0,0) und y ≠ (1,0,0)
          -- Wir müssen einen extra Fall für y = (1,0,0) machen, unser Pfad in diesem fall besonders definiert werden muss,
          --  damit keine Singularität auftritt.
          cases eq_or_ne y (-1, 0, 0) with h h,
          {
            simp [h],
          },
          {
            -- wenn y ≠ (1,0,0)
            rw if_neg h,
            -- wir möchten hier zeigen, dass wenn wir y durch die Norm von y teilen, dass y wieder rauskommt, wenn y in S2 liegt
            simp [S2] at hy,
            rw hy,
            simp,
          },
        end,
        -- target' := _,
        -- außerdem steht dort `extends C(I, X)`, also brauchen wir noch:
        -- hier soll eine funktion definiert werden, welche [0,1] nach ℝ×ℝ×ℝ geht
        -- sie soll für t = 0 den wert (1,0,0) haben und für t = 1 den wert y
        -- wir müssen auf jeden Fall für jeden wert t zwischen 0 und 1 einen wert p in ℝ×ℝ×ℝ haben, mit ‖p‖ = 1
        to_fun := λ t,
          if y = (-1,0,0) then
            (real.cos (coe t * real.pi), real.sin (coe t * real.pi), 0)
          else
            let v := (1 - (coe t : ℝ)) • (1,0,0) + (coe t : ℝ) • y in
            (1 / ‖v‖) • v,
        continuous_to_fun := by sorry,
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