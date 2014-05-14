Require Import
  Utf8 Containers.Maps String ToString
  Integers Coqlib
  TreeAl
  LatticeSignatures AdomLib
  DebugAbMachineNonrel
  AbMachineNonrel
  Goto AbGoto GotoAnalysis.

Section CFG.

Variables t d: Type.
Variables (D: ab_machine_int d) (T: mem_dom t d).

  Definition node : Type := int.

  Existing Instances OT_ints.
  Definition node_set : Type := Map [ node, unit ].
  Definition node_graph : Type := Map [ node, list (node * option (ab_instruction d)) * bool ].
  (* boolean indicates if node is final*)

  Variable E : Map [ node, t ].
  Variable max_deref: N.

  Definition ab_post_many' (pp:node) (m:t) : list (ab_post_res t d * option (ab_instruction d)) :=
    match abstract_decode_at D T max_deref pp m with
    | Just instr => flat_map (λ k,
                              List.map (λ r, (r, Some (fst k)))
                                       (ab_post_single D T max_deref m pp k)
                             ) instr
    | All => (GiveUp t d, None) :: nil
    end.

  Definition successors (i: node) : list (node * option (ab_instruction d)) * bool :=
    match (E)[i] with
    | None => (nil, false)
    | Some mc =>
      let res := ab_post_many' i mc in
      @List.fold_left
        (list (node * option (ab_instruction d)) * bool)
        (ab_post_res t d * option (ab_instruction d))
        (fun sf r =>
           let (s, f) := sf in
           match r with
           | (Run j _, i) => ((j, i)::s, f)
           | (Hlt _,   _) => (s, true)
           | (GiveUp, _) =>
             print
               ("CFG.successors: gave up on node " ++ to_string i)%string
             (s, f) (* may happen because of vp_forget *)
           end
        )
        res
        (nil, false)
    end.

  Fixpoint compute_cfg' (fuel: nat) (w: list node) (s: node_set) (g: node_graph)
           { struct fuel }
  : option node_graph :=
    match fuel with
      | O => None
      | S fuel' =>
        match w with
          | i::w' =>
            let (succ, f) := successors i in
            let '(edges, w, s) :=
                @List.fold_left (list (node * option (ab_instruction d)) * list node * node_set) _
                  (fun ews j =>
                     let '(e, w, s) := ews in
                     let e := j :: e in
                     let w := match s [fst j] with
                                | Some tt => w
                                | None => fst j :: w
                              end in
                     let s := s [ fst j <- tt ] in
                     (e, w, s)
                  )
                  succ
                  (nil, w', s)
            in
            compute_cfg' fuel' w s (MapInterface.add i (edges, f) g)
          | nil => Some g
        end
    end.

  Definition compute_cfg fuel : option node_graph :=
    compute_cfg' fuel (Int.zero :: nil) ([] [ Int.zero <- tt ]) [].

  Definition cfg_fold {A: Type} (f: node → list (node * option (ab_instruction d)) * bool → A → A)
             (g: node_graph) (z: A) : A :=
    MapInterface.fold f g z.

End CFG.
