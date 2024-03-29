/-
Copyright (c) 2019 Jesse Michael Han. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Jesse Michael Han 

A simplified version of the coffee can problem, from David Gries' The Science of Programming

Given a coffee can filled with finitely many black and white beans, and an infinite supply of white beans, carry out the following procedure: as long as there is more than one bean in the can,

 - Draw two beans.
 - If their colors are different, discard the white one and return the black one to the can.
 - If their colors are the same, discard both of them and add a white bean to the can.

Prove that if the number of black beans in the can is odd, then the process always ends with a black bean, and that if the number of black beans in the can is even, then the process always ends with a white bean.
-/

import tactic
import data.nat.parity

@[derive decidable_eq, derive has_reflect]
inductive beans : Type
| white : beans
| black : beans

instance : has_repr beans :=
{ repr := λ b, beans.cases_on b "white" "black" }

open beans

@[simp]def count_black : list beans → ℕ
| [] := 0
| (white::xs) := count_black xs
| (black::xs) := count_black xs + 1

@[simp]def count_white : list beans → ℕ
| [] := 0
| (white::xs) := count_white xs + 1
| (black::xs) := count_white xs

@[simp]lemma count_eq_length (xs : list beans) : count_black xs + count_white xs = xs.length :=
begin
  induction xs with x_hd x_tl ih,
    { refl },
    { cases x_hd; simp [ih.symm] }
end

def coffee : list beans → list beans
| [] := []
| [x] := [x]
| (black::white::xs) := coffee (black::xs)
| (white::black::xs) := coffee (black::xs)
| (black::black::xs) := coffee (white::xs)
| (white::white::xs) := coffee (white::xs)

@[simp]lemma coffee_singleton {x : beans} : coffee [x] = [x] :=
beans.cases_on x rfl rfl

def some_beans : list beans := [black, white, black, black, white, black, white, black, black, white, black]

#eval coffee some_beans
-- [black]

section metaprogramming

meta instance : has_to_format beans :=
{ to_format := λ b, beans.cases_on b (format.of_string "white") (format.of_string "black") }

meta def coffee_eval : list beans → tactic unit
| [] := tactic.trace "[]"
| [x] := tactic.trace format!"final state: [{x}]"
| arg@(black::white::xs) := 
  do  tactic.trace format!"current state: {arg}",
      tactic.trace "got black + white, discarding white",
      coffee_eval (black::xs)
| arg@(white::black::xs) :=
  do  tactic.trace format!"current state: {arg}",
      tactic.trace "got white + black, discarding white",
      coffee_eval (black::xs)
| arg@(black::black::xs) :=
  do  tactic.trace format!"current state: {arg}",
      tactic.trace "got black + black, discarding both and adding white",
      coffee_eval (white::xs)
| arg@(white::white::xs) :=
  do tactic.trace format!"current state: {arg}",
     tactic.trace "got white + white, discarding white",
     coffee_eval (white::xs)

@[reducible]meta def my_parser := state_t string tactic

meta def beans.of_string : my_parser beans :=
⟨ λ ⟨cs⟩, match cs with
         | [] := tactic.failed
         | (x::xs) := if x = '0' then return (white, ⟨xs⟩) else
                      if x = '1' then return (black, ⟨xs⟩) else
                      tactic.failed
         end ⟩

meta def repeat {α} : my_parser α → my_parser (list α) :=
λ p, (list.cons) <$> p <*> (repeat p <|> return [])

meta def my_parser.run {α} [has_to_tactic_format α] (p : my_parser α) (arg : string) : tactic α :=
do bs <- prod.fst <$> state_t.run p arg,
   tactic.trace bs,
   return bs

meta def parse_beans (arg : string) : tactic unit :=
do bs <- my_parser.run (repeat beans.of_string) arg,
   tactic.exact `(bs).to_expr

end metaprogramming

section test

def some_more_beans : list beans := by {parse_beans "10110001011"}

run_cmd coffee_eval some_more_beans

end test

@[simp]lemma coffee_white {x} {xs} : coffee (white::x::xs) = coffee (x::xs) :=
begin
  cases x,
    { rw coffee },
    { simp [coffee] },
end

lemma coffee_black_white {x} {xs} : coffee (x::xs) = [black] ∨ coffee (x::xs) = [white] :=
begin
  induction xs with y xs ih generalizing x,
    { cases x; simp },
    { cases x; cases y; simp [*,coffee] }
end

open nat

lemma coffee_parity_aux (xs : list beans) (k : ℕ) (H_k : k = xs.length) : even (count_black xs) ↔ even (count_black (coffee xs)) :=
begin
  revert xs H_k, apply nat.strong_induction_on k, clear k,
  intros n IH xs Hn,
  cases xs with x xs,
    { simp [coffee] },
    { cases xs with y xs,
      { simp [coffee] },
      { cases x; cases y,
          { simp [coffee] with parity_simps,
            rw ← IH (xs.length + 1) (by norm_num*),
            { simp },
            { refl }},
          { simp [coffee], rw ← IH (xs.length + 1) (by norm_num*),
            { simp },
            { refl }},
          { simp [coffee], rw ← IH (xs.length + 1) (by norm_num*),
            { simp },
            { refl }},
          { simp [coffee] with parity_simps,
            rw ← IH (xs.length + 1) (by norm_num*),
            { simp },
            { refl }}}}
end

lemma coffee_parity {xs : list beans} : even (count_black xs) ↔ even (count_black (coffee xs)) :=
coffee_parity_aux xs xs.length rfl

theorem ends_black_of_count_black_odd {x} {xs : list beans} (H_odd : ¬ (even $ count_black $ x::xs)) : coffee (x::xs) = [black] :=
by {have := @coffee_parity (x::xs), have := @coffee_black_white x xs, finish}

theorem ends_white_of_count_black_even {x} {xs : list beans} (H_even : even $ count_black $ x::xs) : coffee (x::xs) = [white] :=
by {have := @coffee_parity (x::xs), have := @coffee_black_white x xs, finish}
