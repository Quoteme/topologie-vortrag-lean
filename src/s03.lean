import topology.basic
import topology.path_connected
import analysis.normed_space.basic
import data.set.basic
import s01
import s02

/-
## 1.2 Wann ist ein topologischer Raum (weg-)zusammenhängend?

Damit ein Raum zusammenhängend ist, muss er eine instanz der Klasse
`connected_space` sein.
-/

#check connected_space
#check is_connected

/-
Wir möchten nun zeigen, dass `I` ein zusammenhängender Raum ist.

Zuerst zeigen wir, dass unsere Definition des Einheitsintervalles die
selbe ist, wie die, welche in Lean bereits definiert ist.
Das wird unseren Beweis im kommenden vereinfachen
-/

lemma I_is_unit_interval : I = unit_interval := 
  begin
    split,
  end

-- class Coe (α : unit_interval) (β : I) :=
--   (coe : α.val = β.val)

-- instance : Coe unit_interval I :=
--   ⟨λ x, x.val, λ x, x.property⟩

/-
Nachdem wir nun gezeigt haben, dass unsere Definition des Einheitsintervalles
die selbe ist, wie die, welche in Lean bereits definiert ist, können wir
zeigen, dass unser Einheitsintervall (weg-) zusammenhängend ist.
-/

example : is_path_connected I :=
  begin
    -- zuerst möchten wir die Definition von "wegzusammenhängend" aufbröseln
    unfold is_path_connected,
    -- damit ein topologischer Raum wegzusammenhängend ist, muss es
    -- nach der Definition von Lean einen Punkt geben, sodass es von diesem
    -- Punkt zu jedem anderen Punkt einen Pfad gibt.
    -- Wir benutzen dafür den Punkt 0
    use 0,
    split,
      begin
        -- Zuerst müssen wir zeigen, dass 0 wirklich in unserem Raum, dem Einheitsintervall liegt
        by split; linarith,
      end,
      begin
        -- Jetzt müssen wir noch zeigen, dass jedes andere Element in unserem Raum
        -- durch ein Eleement vom Typen "path", also einen Pfad, verbunden ist.
        intros y h,
        unfold joined_in,
        -- Wir möchten nun diesen Pfad konstruieren.
        let f : path 0 y := { to_fun := (λ t, t*y),
        continuous_to_fun := by continuity, 
        source' := by simp,
        target' := by simp,
        },
        use f,
        -- wir möchten nun noch zeigen, dass jedes Element,
        -- welches von $f$ getroffen wird, auch in $I$ liegt.
        intro y',
        simp,
        -- wir zeigen nun, dass wenn $y$ und $y_1$ in $I$ liegen, dann auch $y*y_1$ in $I$ liegt.
        split,
        { 
          apply mul_nonneg,
          {
            -- zeige hier, dass $y$ größer gleich 0 ist, wenn es aus $I$ kommt
            -- rewrite anwenden
            simp [I] at h,
            rcases h with ⟨h1, h2⟩,
            -- unfold unit_interval at y',
            -- norm_cast at h1,
            -- let y'' :  := coe y',
            have lal := y'.property,
            rcases lal with ⟨lal1, lal2⟩,
            assumption,
          },
          {
            -- zeige hier, dass $y$ größer gleich 0 ist, wenn es aus $I$ kommt
            -- simp [set.mem_def] at h,
            rcases h with ⟨h1, h2⟩,
            assumption,
          }
        },
        {
          -- TODO: Hier sollte noch gezeigt werden, dass 
          sorry
        },
      end
  end

-- example : is_connected I := 
--   begin
--   split,
--     begin
--       -- wir zeigen, dass `I` nicht leer ist, indem wir ein Element angeben.
--       use ⟨0, by split; linarith⟩, 
--     end,
--     begin
--       
--     end
--   end