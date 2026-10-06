(* Combinatorial encoding of string diagrams *)
type diagram = {
  s : int;          (* D.S: number of source edges *)
  n : int;          (* D.N: diagram height / number of vertices[cite: 1] *)
  h : int array;    (* D.H: vertex horizontal positions[cite: 1] *)
  i : int array;    (* D.I: vertex source size[cite: 1] *)
  o : int array;    (* D.O: vertex target size[cite: 1] *)
}

(* Calculates D.\Delta(n) = D.O(n) - D.I(n)[cite: 1] *)
let delta d n = d.o.(n) - d.i.(n)

(* Calculates wires at each level D.W(n)[cite: 1] *)
let wires d n_level =
  let w = ref d.s in
  for k = 0 to n_level - 1 do
    w := !w + delta d k
  done;
  !w

(* Checks if a right exchange is admissible at height n[cite: 1] *)
let admits_right_exchange d n =
  if n >= d.n - 1 then false
  else d.h.(n) >= d.h.(n + 1) + d.i.(n + 1)

(* Performs a right exchange D_{R,n} at height n[cite: 1] *)
let right_exchange d n =
  let h_new = Array.copy d.h in
  let i_new = Array.copy d.i in
  let o_new = Array.copy d.o in
  
  h_new.(n) <- d.h.(n + 1);
  i_new.(n) <- d.i.(n + 1);
  o_new.(n) <- d.o.(n + 1);
  
  h_new.(n + 1) <- d.h.(n) + delta d (n + 1);
  i_new.(n + 1) <- d.i.(n);
  o_new.(n + 1) <- d.o.(n);
  
  { d with h = h_new; i = i_new; o = o_new }

(* 
   Normalizes a connected diagram using the right exchange rewrite strategy.
   This algorithm terminates in O(v^3) steps for boundary-connected diagrams[cite: 1].
*)
let rec normalize_connected d =
  let rec find_exchange idx =
    if idx >= d.n - 1 then None
    else if admits_right_exchange d idx then Some idx
    else find_exchange (idx + 1)
  in
  match find_exchange 0 with
  | Some n -> normalize_connected (right_exchange d n)
  | None -> d

(* 
   Extension to disconnected diagrams via Structural Trees.
   A structural tree is a complete invariant for diagram equivalence[cite: 1].
*)
type structural_tree = face_node
and face_node = component_node list
and component_node = {
  norm_root : diagram;
  faces : face_node list;
}

(* 
   Algorithm 6.2: Recursively computes a canonical representation (sorting) 
   for a structural tree to handle disconnected components[cite: 1].
*)
let rec compare_face_nodes (f1 : face_node) (f2 : face_node) =
  let sorted_f1 = List.sort compare_component_nodes f1 in
  let sorted_f2 = List.sort compare_component_nodes f2 in
  compare sorted_f1 sorted_f2

and compare_component_nodes c1 c2 =
  (* Assumes a structural comparison 'compare_diagrams' exists for normalized components *)
  let cmp = compare c1.norm_root c2.norm_root in
  if cmp <> 0 then cmp
  else 
    let rec compare_face_lists l1 l2 =
      match l1, l2 with
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | h1::t1, h2::t2 ->
          let c = compare_face_nodes h1 h2 in
          if c <> 0 then c else compare_face_lists t1 t2
    in
    compare_face_lists c1.faces c2.faces

let normalize_disconnected (tree : structural_tree) : structural_tree =
  let rec sort_face_node (f : face_node) =
    List.map sort_component_node f
    |> List.sort compare_component_nodes
  and sort_component_node (c : component_node) =
    {
      norm_root = normalize_connected c.norm_root;
      faces = List.map sort_face_node c.faces; (* Order preserved by initial introduction[cite: 1] *)
    }
  in
  sort_face_node tree