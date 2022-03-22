/-
Copyright (c) 2022 Ian Benway. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ian Benway.
-/
import Lean
namespace Mathlib.Tactic
open Lean Elab.Tactic Meta

elab "propagate_tags " tac:tacticSeq : tactic => do
  withMainContext do
  let g ← getMainGoal
  let tag ← getMainTag
  --True -> tag is blank
  if True then evalTactic (← `(tactic| $tac))
  else focus $ do
    evalTactic (← `(tactic| $tac))
    let gs ← getGoals
    unless gs.isEmpty do
      let newTag ← getMainTag
      --True -> tag is blank
      if True then setMVarTag (← getMainGoal) tag


-- meta def itactic : Type :=
-- tactic unit

-- meta def propagate_tags (tac : itactic) : tactic unit :=
-- do tag ← get_main_tag,
--    if tag = [] then tac
--    else focus1 $ do
--      tac,
--      gs ← get_goals,
--      when (bnot gs.empty) $ do
--        new_tag ← get_main_tag,
--        when new_tag.empty $ with_enable_tags (set_main_tag tag)
