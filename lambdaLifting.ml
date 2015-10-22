open Closure

let toplevel : fundef list ref = ref []
let global_map = ref M.empty

(*
 * KNormal.t中に存在する自由変数と，除去済みのKNormal.tを返す関数
 * (env: Id.t list, exp: Knormal.t) -> (fvs: Id.t list, exp: KNormal.t)
 *)
let rec fv env = function
  | KNormal.Unit -> ([], KNormal.Unit)
  | KNormal.Int(i) -> ([], KNormal.Int(i))
  | KNormal.Float(d) -> ([], KNormal.Float(d))
  | KNormal.Neg(x) ->
      ((if List.mem x env then [] else [x]), KNormal.Neg(x))
  | KNormal.FNeg(x) ->
      ((if List.mem x env then [] else [x]), KNormal.FNeg(x))
  | KNormal.Var(x) ->
      ((if List.mem x env then [] else [x]), KNormal.Var(x))
  | KNormal.Add(x, y) ->
      (List.filter (fun x -> not (List.mem x env)) [x;y], KNormal.Add(x, y))
  | KNormal.Sub(x, y) ->
      (List.filter (fun x -> not (List.mem x env)) [x;y], KNormal.Sub(x, y))
  | KNormal.FAdd(x, y) ->
      (List.filter (fun x -> not (List.mem x env)) [x;y], KNormal.FAdd(x, y))
  | KNormal.FSub(x, y) ->
      (List.filter (fun x -> not (List.mem x env)) [x;y], KNormal.FSub(x, y))
  | KNormal.FMul(x, y) ->
      (List.filter (fun x -> not (List.mem x env)) [x;y], KNormal.FMul(x, y))
  | KNormal.FDiv(x, y) ->
      (List.filter (fun x -> not (List.mem x env)) [x;y], KNormal.FDiv(x, y))
  | KNormal.IfEq(x, y, e1, e2) ->
      let fv1, e1' = fv env e1 in
      let fv2, e2' = fv env e2 in
      (List.flatten [
        List.filter (fun x -> not (List.mem x env)) [x;y]; fv1; fv2],
       KNormal.IfEq(x, y, e1', e2'))
  | KNormal.IfLE(x, y, e1, e2) ->
      let fv1, e1' = fv env e1 in
      let fv2, e2' = fv env e2 in
      (List.flatten [
        List.filter (fun x -> not (List.mem x env)) [x;y]; fv1; fv2],
       KNormal.IfLE(x, y, e1', e2'))
  | KNormal.Let((x, t), e1, e2) ->
      if not (M.mem x !global_map) then
        global_map := M.add x t !global_map;
      let env' = x :: env in
      let fv1, e1' = fv env' e1 in
      let fv2, e2' = fv env' e2 in
      (List.flatten [fv1; fv2], KNormal.Let((x, t), e1', e2'))
  | KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts; KNormal.body = e1 }, e2) ->
      global_map := M.add_list yts !global_map;
      (* 
       * 関数本体は関数名と引数のみの環境で評価
       * (外部環境に存在する識別子は自由変数)
       *)
      let env1 = x :: (List.map fst yts) in
      (* 評価部は関数名を外部環境に加えた環境で評価 *)
      let env2 = x :: env in
      let fv1, e1' = fv env1 e1 in
      let fv2, e2' = fv env2 e2 in
      (*
       * 自由変数除去のために呼び出し時に自由変数をわたすよう引数を追加する
       * Closure.fundef.args : (Id.t * Type.t)なので、
       * 自由変数の型を推定する必要がある(Int/Float)
       * => 整数レジスタ/浮動小数点レジスタのどちらにallocされるか決まる
       *)
      let yts' = List.flatten [yts; List.map (fun x -> (x, M.find x !global_map)) fv1] in
      ([],
       KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts'; KNormal.body = e1' }, e2'))
  | KNormal.App(f, xs) ->
      (List.filter (fun x -> not (List.mem x env)) xs, KNormal.App(f, xs))
  | KNormal.Tuple(xs) ->
      (List.filter (fun x -> not (List.mem x env)) xs, KNormal.Tuple(xs))
  | KNormal.LetTuple(xts, y, e) ->
      global_map := M.add_list xts !global_map;
      let env' = List.flatten [List.map fst xts; env] in
      let fvs, e' = fv env' e in
      ((if not (List.mem y env) then fvs else y :: fvs), KNormal.LetTuple(xts, y, e'))
  | KNormal.Get(x, y) ->
      (List.filter (fun x -> not (List.mem x env)) [x;y], KNormal.Get(x, y))
  | KNormal.Put(x, y, z) ->
      (List.filter (fun x -> not (List.mem x env)) [x;y;z], KNormal.Put(x, y, z))
  | KNormal.ExtArray(x) ->
      ((if not (List.mem x env) then [] else [x]), KNormal.ExtArray(x))
  | KNormal.ExtFunApp(x, ys) ->
      (List.filter (fun x -> not (List.mem x env)) ys, KNormal.ExtFunApp(x, ys))

(*
 * KNormal.t -> Closure.t
 *)
let rec conv = function
  | KNormal.Unit -> Closure.Unit
  | KNormal.Int(i) -> Closure.Int(i)
  | KNormal.Float(d) -> Closure.Float(d)
  | KNormal.Neg(x) -> Closure.Neg(x)
  | KNormal.FNeg(x) -> Closure.FNeg(x)
  | KNormal.Var(x) -> Closure.Var(x)
  | KNormal.Add(x, y) -> Closure.Add(x, y)
  | KNormal.Sub(x, y) -> Closure.Sub(x, y)
  | KNormal.FAdd(x, y) -> Closure.FAdd(x, y)
  | KNormal.FSub(x, y) -> Closure.FSub(x, y)
  | KNormal.FMul(x, y) -> Closure.FMul(x, y)
  | KNormal.FDiv(x, y) -> Closure.FDiv(x, y)
  | KNormal.IfEq(x, y, e1, e2) -> Closure.IfEq(x, y, conv e1, conv e2)
  | KNormal.IfLE(x, y, e1, e2) -> Closure.IfLE(x, y, conv e1, conv e2)
  | KNormal.Let((x, t), e1, e2) -> Closure.Let((x, t), conv e1, conv e2)
  | KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts; KNormal.body = e1 }, e2) ->
      failwith "at this point, all function must be added to toplevel."
  | KNormal.App(f, xs) -> Closure.AppDir(Id.L(f), xs)
  | KNormal.Tuple(xs) -> Closure.Tuple(xs)
  | KNormal.LetTuple(xts, y, e) -> Closure.LetTuple(xts, y, conv e)
  | KNormal.Get(x, y) -> Closure.Get(x, y)
  | KNormal.Put(x, y, z) -> Closure.Put(x, y, z)
  | KNormal.ExtArray(x) -> Closure.ExtArray(Id.L(x))
  | KNormal.ExtFunApp(x, ys) -> Closure.AppDir(Id.L("min_caml_" ^ x), ys)

(*
 * 自由変数を持たない関数をtoplevelに追加する
 * KNormal.t -> KNormal.t
 *)
let rec lifting env = function
  | KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts; KNormal.body = e1 }, e2) ->
      (* 
       * 関数本体は関数名と引数のみの環境で評価
       * (外部環境に存在する識別子は自由変数)
       *)
      let env1 = x :: (List.map fst yts) in
      (* 評価部は関数名を外部環境に加えた環境で評価 *)
      let env2 = x :: env in
      if fst (fv env1 e1) = [] && not (exists_letrec e1) then
        (* 
         * 関数本体に自由変数もローカル変数もない場合
         * => toplevelに関数をliftingし、評価部のliftingを行う
         *)
        (toplevel := {
          name = (Id.L(x), t);
          args = yts;
          formal_fv = [];
          body = conv e1 } :: !toplevel;
        lifting env2 e2)
      else
        (*
         * それ以外の場合はとりあえずローカル関数を残しておく
         * iterationで繰り返していく過程のどこかでliftingされる
         *)
        KNormal.LetRec({
          KNormal.name = (x, t);
          KNormal.args = yts;
          KNormal.body = lifting env1 e1}, lifting env2 e2)
  | KNormal.IfEq(x, y, e1, e2) ->
      KNormal.IfEq(x, y, lifting env e1, lifting env e2)
  | KNormal.IfLE(x, y, e1, e2) ->
      KNormal.IfLE(x, y, lifting env e1, lifting env e2)
  | KNormal.Let((x, t), e1, e2) ->
      KNormal.Let((x, t), lifting (x :: env) e1, lifting (x :: env) e2)
  | KNormal.LetTuple(xts, y, e) ->
      let env' = List.flatten [List.map (fun (x, _) -> x) xts ; env] in
      KNormal.LetTuple(xts, y, lifting env' e)
  | KNormal.App(x, xs) -> (* 関数適用の場合 *)
      (* グローバル関数の関数名をリストとして取得 *)
      let global_fs = List.map (fun f -> fst (f.name)) !toplevel in
      if List.mem (Id.L(x)) global_fs then
        (*
         * 適用する関数がグローバル関数の場合
         * => 自由変数を呼び出し時の引数に加える
         *)
        let fd = List.find (fun f -> fst (f.name) = (Id.L(x))) !toplevel in
        let fvargs = List.map (fun (x, _) -> x) (fd.args) in
        let fvargs = List.filter (fun arg -> List.mem arg env) fvargs in
        KNormal.App(x, xs @ fvargs)
      else
        KNormal.App(x, xs)
  | e -> e
(* ローカル関数が存在するかどうか判定 *)
and exists_letrec = function
  | KNormal.LetRec(_, _) -> true
  | KNormal.IfEq(x, y, e1, e2) -> exists_letrec e1 || exists_letrec e2
  | KNormal.IfLE(x, y, e1, e2) -> exists_letrec e1 || exists_letrec e2
  | KNormal.Let((x, t), e1, e2) -> exists_letrec e1 || exists_letrec e2
  | KNormal.LetTuple(xts, y, e) -> exists_letrec e
  | _ -> false

(*
 * ローカル関数がなくなるまでLambda Liftingを繰り返す
 *)
let rec iteration e =
  let fv, e' = fv [] e in
  let e' = lifting [] e' in
  if exists_letrec e' then
    iteration e'
  else
    e'

let f e =
  toplevel := [];
  let e' = iteration e in
  Prog(List.rev !toplevel, conv e')
