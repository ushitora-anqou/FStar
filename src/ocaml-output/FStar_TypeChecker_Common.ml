open Prims
type rel =
  | EQ 
  | SUB 
  | SUBINV 
let (uu___is_EQ : rel -> Prims.bool) =
  fun projectee  -> match projectee with | EQ  -> true | uu____37 -> false 
let (uu___is_SUB : rel -> Prims.bool) =
  fun projectee  -> match projectee with | SUB  -> true | uu____48 -> false 
let (uu___is_SUBINV : rel -> Prims.bool) =
  fun projectee  ->
    match projectee with | SUBINV  -> true | uu____59 -> false
  
type rank_t =
  | Rigid_rigid 
  | Flex_rigid_eq 
  | Flex_flex_pattern_eq 
  | Flex_rigid 
  | Rigid_flex 
  | Flex_flex 
let (uu___is_Rigid_rigid : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rigid_rigid  -> true | uu____70 -> false
  
let (uu___is_Flex_rigid_eq : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_rigid_eq  -> true | uu____81 -> false
  
let (uu___is_Flex_flex_pattern_eq : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_flex_pattern_eq  -> true | uu____92 -> false
  
let (uu___is_Flex_rigid : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_rigid  -> true | uu____103 -> false
  
let (uu___is_Rigid_flex : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rigid_flex  -> true | uu____114 -> false
  
let (uu___is_Flex_flex : rank_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Flex_flex  -> true | uu____125 -> false
  
type 'a problem =
  {
  pid: Prims.int ;
  lhs: 'a ;
  relation: rel ;
  rhs: 'a ;
  element: FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ;
  logical_guard: FStar_Syntax_Syntax.term ;
  logical_guard_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  reason: Prims.string Prims.list ;
  loc: FStar_Range.range ;
  rank: rank_t FStar_Pervasives_Native.option }
let __proj__Mkproblem__item__pid : 'a . 'a problem -> Prims.int =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> pid
  
let __proj__Mkproblem__item__lhs : 'a . 'a problem -> 'a =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> lhs
  
let __proj__Mkproblem__item__relation : 'a . 'a problem -> rel =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> relation
  
let __proj__Mkproblem__item__rhs : 'a . 'a problem -> 'a =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> rhs
  
let __proj__Mkproblem__item__element :
  'a . 'a problem -> FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> element
  
let __proj__Mkproblem__item__logical_guard :
  'a . 'a problem -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> logical_guard
  
let __proj__Mkproblem__item__logical_guard_uvar :
  'a . 'a problem -> FStar_Syntax_Syntax.ctx_uvar =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> logical_guard_uvar
  
let __proj__Mkproblem__item__reason :
  'a . 'a problem -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> reason
  
let __proj__Mkproblem__item__loc : 'a . 'a problem -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> loc
  
let __proj__Mkproblem__item__rank :
  'a . 'a problem -> rank_t FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { pid; lhs; relation; rhs; element; logical_guard; logical_guard_uvar;
        reason; loc; rank;_} -> rank
  
type prob =
  | TProb of FStar_Syntax_Syntax.typ problem 
  | CProb of FStar_Syntax_Syntax.comp problem 
let (uu___is_TProb : prob -> Prims.bool) =
  fun projectee  ->
    match projectee with | TProb _0 -> true | uu____553 -> false
  
let (__proj__TProb__item___0 : prob -> FStar_Syntax_Syntax.typ problem) =
  fun projectee  -> match projectee with | TProb _0 -> _0 
let (uu___is_CProb : prob -> Prims.bool) =
  fun projectee  ->
    match projectee with | CProb _0 -> true | uu____580 -> false
  
let (__proj__CProb__item___0 : prob -> FStar_Syntax_Syntax.comp problem) =
  fun projectee  -> match projectee with | CProb _0 -> _0 
let (as_tprob : prob -> FStar_Syntax_Syntax.typ problem) =
  fun uu___0_602  ->
    match uu___0_602 with
    | TProb p -> p
    | uu____608 -> failwith "Expected a TProb"
  
type probs = prob Prims.list
type guard_formula =
  | Trivial 
  | NonTrivial of FStar_Syntax_Syntax.formula 
let (uu___is_Trivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | Trivial  -> true | uu____628 -> false
  
let (uu___is_NonTrivial : guard_formula -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonTrivial _0 -> true | uu____640 -> false
  
let (__proj__NonTrivial__item___0 :
  guard_formula -> FStar_Syntax_Syntax.formula) =
  fun projectee  -> match projectee with | NonTrivial _0 -> _0 
type deferred = (Prims.string * prob) Prims.list
type univ_ineq =
  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
let (mk_by_tactic :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun tac  ->
    fun f  ->
      let t_by_tactic =
        let uu____672 =
          FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid  in
        FStar_Syntax_Syntax.mk_Tm_uinst uu____672
          [FStar_Syntax_Syntax.U_zero]
         in
      let uu____673 =
        let uu____674 = FStar_Syntax_Syntax.as_arg tac  in
        let uu____683 =
          let uu____694 = FStar_Syntax_Syntax.as_arg f  in [uu____694]  in
        uu____674 :: uu____683  in
      FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____673
        FStar_Range.dummyRange
  
let rec (delta_depth_greater_than :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth -> Prims.bool)
  =
  fun l  ->
    fun m  ->
      match (l, m) with
      | (FStar_Syntax_Syntax.Delta_equational_at_level
         i,FStar_Syntax_Syntax.Delta_equational_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_constant_at_level
         i,FStar_Syntax_Syntax.Delta_constant_at_level j) -> i > j
      | (FStar_Syntax_Syntax.Delta_abstract d,uu____749) ->
          delta_depth_greater_than d m
      | (uu____750,FStar_Syntax_Syntax.Delta_abstract d) ->
          delta_depth_greater_than l d
      | (FStar_Syntax_Syntax.Delta_equational_at_level uu____752,uu____753)
          -> true
      | (uu____756,FStar_Syntax_Syntax.Delta_equational_at_level uu____757)
          -> false
  
let rec (decr_delta_depth :
  FStar_Syntax_Syntax.delta_depth ->
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun uu___1_767  ->
    match uu___1_767 with
    | FStar_Syntax_Syntax.Delta_constant_at_level _770 when
        _770 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_equational_at_level _771 when
        _771 = Prims.int_zero -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_constant_at_level (i - Prims.int_one))
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Delta_equational_at_level (i - Prims.int_one))
    | FStar_Syntax_Syntax.Delta_abstract d -> decr_delta_depth d
  
type identifier_info =
  {
  identifier:
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ;
  identifier_ty: FStar_Syntax_Syntax.typ ;
  identifier_range: FStar_Range.range }
let (__proj__Mkidentifier_info__item__identifier :
  identifier_info ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either)
  =
  fun projectee  ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier
  
let (__proj__Mkidentifier_info__item__identifier_ty :
  identifier_info -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier_ty
  
let (__proj__Mkidentifier_info__item__identifier_range :
  identifier_info -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { identifier; identifier_ty; identifier_range;_} -> identifier_range
  
let (insert_col_info :
  Prims.int ->
    identifier_info ->
      (Prims.int * identifier_info) Prims.list ->
        (Prims.int * identifier_info) Prims.list)
  =
  fun col  ->
    fun info  ->
      fun col_infos  ->
        let rec __insert aux rest =
          match rest with
          | [] -> (aux, [(col, info)])
          | (c,i)::rest' ->
              if col < c
              then (aux, ((col, info) :: rest))
              else __insert ((c, i) :: aux) rest'
           in
        let uu____1053 = __insert [] col_infos  in
        match uu____1053 with
        | (l,r) -> FStar_List.append (FStar_List.rev l) r
  
let (find_nearest_preceding_col_info :
  Prims.int ->
    (Prims.int * identifier_info) Prims.list ->
      identifier_info FStar_Pervasives_Native.option)
  =
  fun col  ->
    fun col_infos  ->
      let rec aux out uu___2_1174 =
        match uu___2_1174 with
        | [] -> out
        | (c,i)::rest ->
            if c > col
            then out
            else aux (FStar_Pervasives_Native.Some i) rest
         in
      aux FStar_Pervasives_Native.None col_infos
  
type id_info_by_col = (Prims.int * identifier_info) Prims.list
type col_info_by_row = id_info_by_col FStar_Util.pimap
type row_info_by_file = col_info_by_row FStar_Util.psmap
type id_info_table =
  {
  id_info_enabled: Prims.bool ;
  id_info_db: row_info_by_file ;
  id_info_buffer: identifier_info Prims.list }
let (__proj__Mkid_info_table__item__id_info_enabled :
  id_info_table -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_enabled
  
let (__proj__Mkid_info_table__item__id_info_db :
  id_info_table -> row_info_by_file) =
  fun projectee  ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_db
  
let (__proj__Mkid_info_table__item__id_info_buffer :
  id_info_table -> identifier_info Prims.list) =
  fun projectee  ->
    match projectee with
    | { id_info_enabled; id_info_db; id_info_buffer;_} -> id_info_buffer
  
let (id_info_table_empty : id_info_table) =
  let uu____1285 = FStar_Util.psmap_empty ()  in
  { id_info_enabled = false; id_info_db = uu____1285; id_info_buffer = [] } 
let (id_info__insert :
  (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) ->
    (Prims.int * identifier_info) Prims.list FStar_Util.pimap
      FStar_Util.psmap ->
      identifier_info ->
        (Prims.int * identifier_info) Prims.list FStar_Util.pimap
          FStar_Util.psmap)
  =
  fun ty_map  ->
    fun db  ->
      fun info  ->
        let range = info.identifier_range  in
        let use_range1 =
          let uu____1343 = FStar_Range.use_range range  in
          FStar_Range.set_def_range range uu____1343  in
        let info1 =
          let uu___143_1345 = info  in
          let uu____1346 = ty_map info.identifier_ty  in
          {
            identifier = (uu___143_1345.identifier);
            identifier_ty = uu____1346;
            identifier_range = use_range1
          }  in
        let fn = FStar_Range.file_of_range use_range1  in
        let start = FStar_Range.start_of_range use_range1  in
        let uu____1350 =
          let uu____1357 = FStar_Range.line_of_pos start  in
          let uu____1359 = FStar_Range.col_of_pos start  in
          (uu____1357, uu____1359)  in
        match uu____1350 with
        | (row,col) ->
            let rows =
              let uu____1390 = FStar_Util.pimap_empty ()  in
              FStar_Util.psmap_find_default db fn uu____1390  in
            let cols = FStar_Util.pimap_find_default rows row []  in
            let uu____1436 =
              let uu____1446 = insert_col_info col info1 cols  in
              FStar_All.pipe_right uu____1446 (FStar_Util.pimap_add rows row)
               in
            FStar_All.pipe_right uu____1436 (FStar_Util.psmap_add db fn)
  
let (id_info_insert :
  id_info_table ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Syntax_Syntax.typ -> FStar_Range.range -> id_info_table)
  =
  fun table  ->
    fun id1  ->
      fun ty  ->
        fun range  ->
          let info =
            { identifier = id1; identifier_ty = ty; identifier_range = range
            }  in
          let uu___158_1536 = table  in
          {
            id_info_enabled = (uu___158_1536.id_info_enabled);
            id_info_db = (uu___158_1536.id_info_db);
            id_info_buffer = (info :: (table.id_info_buffer))
          }
  
let (id_info_insert_bv :
  id_info_table ->
    FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> id_info_table)
  =
  fun table  ->
    fun bv  ->
      fun ty  ->
        if table.id_info_enabled
        then
          let uu____1554 = FStar_Syntax_Syntax.range_of_bv bv  in
          id_info_insert table (FStar_Util.Inl bv) ty uu____1554
        else table
  
let (id_info_insert_fv :
  id_info_table ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> id_info_table)
  =
  fun table  ->
    fun fv  ->
      fun ty  ->
        if table.id_info_enabled
        then
          let uu____1574 = FStar_Syntax_Syntax.range_of_fv fv  in
          id_info_insert table (FStar_Util.Inr fv) ty uu____1574
        else table
  
let (id_info_toggle : id_info_table -> Prims.bool -> id_info_table) =
  fun table  ->
    fun enabled  ->
      let uu___170_1590 = table  in
      {
        id_info_enabled = enabled;
        id_info_db = (uu___170_1590.id_info_db);
        id_info_buffer = (uu___170_1590.id_info_buffer)
      }
  
let (id_info_promote :
  id_info_table ->
    (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> id_info_table)
  =
  fun table  ->
    fun ty_map  ->
      let uu___174_1607 = table  in
      let uu____1608 =
        FStar_List.fold_left (id_info__insert ty_map) table.id_info_db
          table.id_info_buffer
         in
      {
        id_info_enabled = (uu___174_1607.id_info_enabled);
        id_info_db = uu____1608;
        id_info_buffer = []
      }
  
let (id_info_at_pos :
  id_info_table ->
    Prims.string ->
      Prims.int ->
        Prims.int -> identifier_info FStar_Pervasives_Native.option)
  =
  fun table  ->
    fun fn  ->
      fun row  ->
        fun col  ->
          let rows =
            let uu____1652 = FStar_Util.pimap_empty ()  in
            FStar_Util.psmap_find_default table.id_info_db fn uu____1652  in
          let cols = FStar_Util.pimap_find_default rows row []  in
          let uu____1659 = find_nearest_preceding_col_info col cols  in
          match uu____1659 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              let last_col =
                let uu____1667 =
                  FStar_Range.end_of_range info.identifier_range  in
                FStar_Range.col_of_pos uu____1667  in
              if col <= last_col
              then FStar_Pervasives_Native.Some info
              else FStar_Pervasives_Native.None
  
let (check_uvar_ctx_invariant :
  Prims.string ->
    FStar_Range.range ->
      Prims.bool ->
        FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.binders -> unit)
  =
  fun reason  ->
    fun r  ->
      fun should_check1  ->
        fun g  ->
          fun bs  ->
            let print_gamma gamma =
              let uu____1714 =
                FStar_All.pipe_right gamma
                  (FStar_List.map
                     (fun uu___3_1727  ->
                        match uu___3_1727 with
                        | FStar_Syntax_Syntax.Binding_var x ->
                            let uu____1730 =
                              FStar_Syntax_Print.bv_to_string x  in
                            Prims.op_Hat "Binding_var " uu____1730
                        | FStar_Syntax_Syntax.Binding_univ u ->
                            Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
                        | FStar_Syntax_Syntax.Binding_lid (l,uu____1736) ->
                            let uu____1753 = FStar_Ident.string_of_lid l  in
                            Prims.op_Hat "Binding_lid " uu____1753))
                 in
              FStar_All.pipe_right uu____1714 (FStar_String.concat "::\n")
               in
            let fail1 uu____1766 =
              let uu____1767 =
                let uu____1769 = FStar_Range.string_of_range r  in
                let uu____1771 = print_gamma g  in
                let uu____1773 = FStar_Syntax_Print.binders_to_string ", " bs
                   in
                FStar_Util.format5
                  "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n"
                  reason uu____1769
                  (if should_check1 then "true" else "false") uu____1771
                  uu____1773
                 in
              failwith uu____1767  in
            if Prims.op_Negation should_check1
            then ()
            else
              (let uu____1786 =
                 let uu____1811 =
                   FStar_Util.prefix_until
                     (fun uu___4_1826  ->
                        match uu___4_1826 with
                        | FStar_Syntax_Syntax.Binding_var uu____1828 -> true
                        | uu____1830 -> false) g
                    in
                 (uu____1811, bs)  in
               match uu____1786 with
               | (FStar_Pervasives_Native.None ,[]) -> ()
               | (FStar_Pervasives_Native.Some
                  (uu____1888,hd1,gamma_tail),uu____1891::uu____1892) ->
                   let uu____1951 = FStar_Util.prefix bs  in
                   (match uu____1951 with
                    | (uu____1976,(x,uu____1978)) ->
                        (match hd1 with
                         | FStar_Syntax_Syntax.Binding_var x' when
                             FStar_Syntax_Syntax.bv_eq x x' -> ()
                         | uu____2006 -> fail1 ()))
               | uu____2007 -> fail1 ())
  
type implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range }
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_reason
  
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_uvar
  
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_tm
  
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_range
  
type implicits = implicit Prims.list
let (implicits_to_string : implicits -> Prims.string) =
  fun imps  ->
    let imp_to_string1 i =
      FStar_Syntax_Print.uvar_to_string
        (i.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
       in
    FStar_Common.string_of_list imp_to_string1 imps
  
type guard_t =
  {
  guard_f: guard_formula ;
  deferred: deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list) ;
  implicits: implicits }
let (__proj__Mkguard_t__item__guard_f : guard_t -> guard_formula) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> guard_f
  
let (__proj__Mkguard_t__item__deferred : guard_t -> deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> deferred
  
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t -> (FStar_Syntax_Syntax.universe Prims.list * univ_ineq Prims.list))
  =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> univ_ineqs
  
let (__proj__Mkguard_t__item__implicits : guard_t -> implicits) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> implicits
  
let (trivial_guard : guard_t) =
  { guard_f = Trivial; deferred = []; univ_ineqs = ([], []); implicits = [] } 
let (conj_guard_f : guard_formula -> guard_formula -> guard_formula) =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (Trivial ,g) -> g
      | (g,Trivial ) -> g
      | (NonTrivial f1,NonTrivial f2) ->
          let uu____2256 = FStar_Syntax_Util.mk_conj f1 f2  in
          NonTrivial uu____2256
  
let (check_trivial : FStar_Syntax_Syntax.term -> guard_formula) =
  fun t  ->
    let uu____2263 =
      let uu____2264 = FStar_Syntax_Util.unmeta t  in
      uu____2264.FStar_Syntax_Syntax.n  in
    match uu____2263 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        Trivial
    | uu____2268 -> NonTrivial t
  
let (imp_guard_f : guard_formula -> guard_formula -> guard_formula) =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (Trivial ,g) -> g
      | (g,Trivial ) -> Trivial
      | (NonTrivial f1,NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let (binop_guard :
  (guard_formula -> guard_formula -> guard_formula) ->
    guard_t -> guard_t -> guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____2311 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____2311;
          deferred = (FStar_List.append g1.deferred g2.deferred);
          univ_ineqs =
            ((FStar_List.append (FStar_Pervasives_Native.fst g1.univ_ineqs)
                (FStar_Pervasives_Native.fst g2.univ_ineqs)),
              (FStar_List.append (FStar_Pervasives_Native.snd g1.univ_ineqs)
                 (FStar_Pervasives_Native.snd g2.univ_ineqs)));
          implicits = (FStar_List.append g1.implicits g2.implicits)
        }
  
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs  -> FStar_List.fold_left conj_guard trivial_guard gs 
let (weaken_guard_formula : guard_t -> FStar_Syntax_Syntax.typ -> guard_t) =
  fun g  ->
    fun fml  ->
      match g.guard_f with
      | Trivial  -> g
      | NonTrivial f ->
          let uu___302_2381 = g  in
          let uu____2382 =
            let uu____2383 = FStar_Syntax_Util.mk_imp fml f  in
            check_trivial uu____2383  in
          {
            guard_f = uu____2382;
            deferred = (uu___302_2381.deferred);
            univ_ineqs = (uu___302_2381.univ_ineqs);
            implicits = (uu___302_2381.implicits)
          }
  
type lcomp =
  {
  eff_name: FStar_Ident.lident ;
  res_typ: FStar_Syntax_Syntax.typ ;
  cflags: FStar_Syntax_Syntax.cflag Prims.list ;
  comp_thunk:
    (unit -> (FStar_Syntax_Syntax.comp * guard_t),FStar_Syntax_Syntax.comp)
      FStar_Util.either FStar_ST.ref
    }
let (__proj__Mklcomp__item__eff_name : lcomp -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> eff_name
  
let (__proj__Mklcomp__item__res_typ : lcomp -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> res_typ
  
let (__proj__Mklcomp__item__cflags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> cflags
  
let (__proj__Mklcomp__item__comp_thunk :
  lcomp ->
    (unit -> (FStar_Syntax_Syntax.comp * guard_t),FStar_Syntax_Syntax.comp)
      FStar_Util.either FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with
    | { eff_name; res_typ; cflags; comp_thunk;_} -> comp_thunk
  
let (mk_lcomp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.cflag Prims.list ->
        (unit -> (FStar_Syntax_Syntax.comp * guard_t)) -> lcomp)
  =
  fun eff_name  ->
    fun res_typ  ->
      fun cflags  ->
        fun comp_thunk  ->
          let uu____2632 = FStar_Util.mk_ref (FStar_Util.Inl comp_thunk)  in
          { eff_name; res_typ; cflags; comp_thunk = uu____2632 }
  
let (lcomp_comp : lcomp -> (FStar_Syntax_Syntax.comp * guard_t)) =
  fun lc  ->
    let uu____2674 = FStar_ST.op_Bang lc.comp_thunk  in
    match uu____2674 with
    | FStar_Util.Inl thunk1 ->
        let uu____2746 = thunk1 ()  in
        (match uu____2746 with
         | (c,g) ->
             (FStar_ST.op_Colon_Equals lc.comp_thunk (FStar_Util.Inr c);
              (c, g)))
    | FStar_Util.Inr c -> (c, trivial_guard)
  
let (apply_lcomp :
  (FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) ->
    (guard_t -> guard_t) -> lcomp -> lcomp)
  =
  fun fc  ->
    fun fg  ->
      fun lc  ->
        mk_lcomp lc.eff_name lc.res_typ lc.cflags
          (fun uu____2846  ->
             let uu____2847 = lcomp_comp lc  in
             match uu____2847 with
             | (c,g) ->
                 let uu____2858 = fc c  in
                 let uu____2859 = fg g  in (uu____2858, uu____2859))
  
let (lcomp_to_string : lcomp -> Prims.string) =
  fun lc  ->
    let uu____2867 = FStar_Options.print_effect_args ()  in
    if uu____2867
    then
      let uu____2871 =
        let uu____2872 = FStar_All.pipe_right lc lcomp_comp  in
        FStar_All.pipe_right uu____2872 FStar_Pervasives_Native.fst  in
      FStar_Syntax_Print.comp_to_string uu____2871
    else
      (let uu____2887 = FStar_Syntax_Print.lid_to_string lc.eff_name  in
       let uu____2889 = FStar_Syntax_Print.term_to_string lc.res_typ  in
       FStar_Util.format2 "%s %s" uu____2887 uu____2889)
  
let (lcomp_set_flags :
  lcomp -> FStar_Syntax_Syntax.cflag Prims.list -> lcomp) =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____2917 -> c
        | FStar_Syntax_Syntax.GTotal uu____2926 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___352_2937 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___352_2937.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___352_2937.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___352_2937.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___352_2937.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___355_2938 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___355_2938.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___355_2938.FStar_Syntax_Syntax.vars)
            }
         in
      mk_lcomp lc.eff_name lc.res_typ fs
        (fun uu____2941  ->
           let uu____2942 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____2942
             (fun uu____2964  ->
                match uu____2964 with | (c,g) -> ((comp_typ_set_flags c), g)))
  
let (is_total_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___5_2990  ->
               match uu___5_2990 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____2994 -> false)))
  
let (is_tot_or_gtot_lcomp : lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals c.eff_name FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.cflags
         (FStar_Util.for_some
            (fun uu___6_3007  ->
               match uu___6_3007 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____3011 -> false)))
  
let (is_lcomp_partial_return : lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.cflags
      (FStar_Util.for_some
         (fun uu___7_3024  ->
            match uu___7_3024 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____3028 -> false))
  
let (is_pure_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (FStar_Syntax_Util.is_pure_effect lc.eff_name))
      ||
      (FStar_All.pipe_right lc.cflags
         (FStar_Util.for_some
            (fun uu___8_3041  ->
               match uu___8_3041 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____3044 -> false)))
  
let (is_pure_or_ghost_lcomp : lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (FStar_Syntax_Util.is_ghost_effect lc.eff_name)
  
let (set_result_typ_lc : lcomp -> FStar_Syntax_Syntax.typ -> lcomp) =
  fun lc  ->
    fun t  ->
      mk_lcomp lc.eff_name t lc.cflags
        (fun uu____3066  ->
           let uu____3067 = FStar_All.pipe_right lc lcomp_comp  in
           FStar_All.pipe_right uu____3067
             (fun uu____3094  ->
                match uu____3094 with
                | (c,g) ->
                    let uu____3111 = FStar_Syntax_Util.set_result_typ c t  in
                    (uu____3111, g)))
  
let (residual_comp_of_lcomp : lcomp -> FStar_Syntax_Syntax.residual_comp) =
  fun lc  ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (lc.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.cflags)
    }
  
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> lcomp) =
  fun c0  ->
    let uu____3126 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3139 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3150 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____3126 with
    | (eff_name,flags) ->
        mk_lcomp eff_name (FStar_Syntax_Util.comp_result c0) flags
          (fun uu____3171  -> (c0, trivial_guard))
  
let (simplify :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun debug  ->
    fun tm  ->
      let w t =
        let uu___404_3197 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___404_3197.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (tm.FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.vars = (uu___404_3197.FStar_Syntax_Syntax.vars)
        }  in
      let simp_t t =
        let uu____3209 =
          let uu____3210 = FStar_Syntax_Util.unmeta t  in
          uu____3210.FStar_Syntax_Syntax.n  in
        match uu____3209 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
            FStar_Pervasives_Native.Some true
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
            FStar_Pervasives_Native.Some false
        | uu____3222 -> FStar_Pervasives_Native.None  in
      let rec args_are_binders args bs =
        match (args, bs) with
        | ((t,uu____3286)::args1,(bv,uu____3289)::bs1) ->
            let uu____3343 =
              let uu____3344 = FStar_Syntax_Subst.compress t  in
              uu____3344.FStar_Syntax_Syntax.n  in
            (match uu____3343 with
             | FStar_Syntax_Syntax.Tm_name bv' ->
                 (FStar_Syntax_Syntax.bv_eq bv bv') &&
                   (args_are_binders args1 bs1)
             | uu____3349 -> false)
        | ([],[]) -> true
        | (uu____3380,uu____3381) -> false  in
      let is_applied bs t =
        if debug
        then
          (let uu____3432 = FStar_Syntax_Print.term_to_string t  in
           let uu____3434 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____3432
             uu____3434)
        else ();
        (let uu____3439 = FStar_Syntax_Util.head_and_args' t  in
         match uu____3439 with
         | (hd1,args) ->
             let uu____3478 =
               let uu____3479 = FStar_Syntax_Subst.compress hd1  in
               uu____3479.FStar_Syntax_Syntax.n  in
             (match uu____3478 with
              | FStar_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if debug
                   then
                     (let uu____3487 = FStar_Syntax_Print.term_to_string t
                         in
                      let uu____3489 = FStar_Syntax_Print.bv_to_string bv  in
                      let uu____3491 = FStar_Syntax_Print.term_to_string hd1
                         in
                      FStar_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu____3487 uu____3489 uu____3491)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu____3496 -> FStar_Pervasives_Native.None))
         in
      let is_applied_maybe_squashed bs t =
        if debug
        then
          (let uu____3514 = FStar_Syntax_Print.term_to_string t  in
           let uu____3516 = FStar_Syntax_Print.tag_of_term t  in
           FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n"
             uu____3514 uu____3516)
        else ();
        (let uu____3521 = FStar_Syntax_Util.is_squash t  in
         match uu____3521 with
         | FStar_Pervasives_Native.Some (uu____3532,t') -> is_applied bs t'
         | uu____3544 ->
             let uu____3553 = FStar_Syntax_Util.is_auto_squash t  in
             (match uu____3553 with
              | FStar_Pervasives_Native.Some (uu____3564,t') ->
                  is_applied bs t'
              | uu____3576 -> is_applied bs t))
         in
      let is_const_match phi =
        let uu____3597 =
          let uu____3598 = FStar_Syntax_Subst.compress phi  in
          uu____3598.FStar_Syntax_Syntax.n  in
        match uu____3597 with
        | FStar_Syntax_Syntax.Tm_match (uu____3604,br::brs) ->
            let uu____3671 = br  in
            (match uu____3671 with
             | (uu____3689,uu____3690,e) ->
                 let r =
                   let uu____3712 = simp_t e  in
                   match uu____3712 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some b ->
                       let uu____3724 =
                         FStar_List.for_all
                           (fun uu____3743  ->
                              match uu____3743 with
                              | (uu____3757,uu____3758,e') ->
                                  let uu____3772 = simp_t e'  in
                                  uu____3772 =
                                    (FStar_Pervasives_Native.Some b)) brs
                          in
                       if uu____3724
                       then FStar_Pervasives_Native.Some b
                       else FStar_Pervasives_Native.None
                    in
                 r)
        | uu____3788 -> FStar_Pervasives_Native.None  in
      let maybe_auto_squash t =
        let uu____3798 = FStar_Syntax_Util.is_sub_singleton t  in
        if uu____3798
        then t
        else FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t
         in
      let squashed_head_un_auto_squash_args t =
        let maybe_un_auto_squash_arg uu____3834 =
          match uu____3834 with
          | (t1,q) ->
              let uu____3855 = FStar_Syntax_Util.is_auto_squash t1  in
              (match uu____3855 with
               | FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
               | uu____3887 -> (t1, q))
           in
        let uu____3900 = FStar_Syntax_Util.head_and_args t  in
        match uu____3900 with
        | (head1,args) ->
            let args1 = FStar_List.map maybe_un_auto_squash_arg args  in
            FStar_Syntax_Syntax.mk_Tm_app head1 args1
              t.FStar_Syntax_Syntax.pos
         in
      let rec clearly_inhabited ty =
        let uu____3978 =
          let uu____3979 = FStar_Syntax_Util.unmeta ty  in
          uu____3979.FStar_Syntax_Syntax.n  in
        match uu____3978 with
        | FStar_Syntax_Syntax.Tm_uinst (t,uu____3984) -> clearly_inhabited t
        | FStar_Syntax_Syntax.Tm_arrow (uu____3989,c) ->
            clearly_inhabited (FStar_Syntax_Util.comp_result c)
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let l = FStar_Syntax_Syntax.lid_of_fv fv  in
            (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
               || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
              || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
        | uu____4013 -> false  in
      let simplify1 arg =
        let uu____4046 = simp_t (FStar_Pervasives_Native.fst arg)  in
        (uu____4046, arg)  in
      let uu____4061 =
        let uu____4062 = FStar_Syntax_Subst.compress tm  in
        uu____4062.FStar_Syntax_Syntax.n  in
      match uu____4061 with
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____4066;
                  FStar_Syntax_Syntax.vars = uu____4067;_},uu____4068);
             FStar_Syntax_Syntax.pos = uu____4069;
             FStar_Syntax_Syntax.vars = uu____4070;_},args)
          ->
          let uu____4100 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____4100
          then
            let uu____4103 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____4103 with
             | (FStar_Pervasives_Native.Some (true ),uu____4161)::(uu____4162,
                                                                   (arg,uu____4164))::[]
                 -> maybe_auto_squash arg
             | (uu____4237,(arg,uu____4239))::(FStar_Pervasives_Native.Some
                                               (true ),uu____4240)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____4313)::uu____4314::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4384::(FStar_Pervasives_Native.Some (false ),uu____4385)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____4455 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____4473 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____4473
             then
               let uu____4476 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____4476 with
               | (FStar_Pervasives_Native.Some (true ),uu____4534)::uu____4535::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____4605::(FStar_Pervasives_Native.Some (true
                              ),uu____4606)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____4676)::
                   (uu____4677,(arg,uu____4679))::[] -> maybe_auto_squash arg
               | (uu____4752,(arg,uu____4754))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____4755)::[]
                   -> maybe_auto_squash arg
               | uu____4828 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____4846 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____4846
                then
                  let uu____4849 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____4849 with
                  | uu____4907::(FStar_Pervasives_Native.Some (true
                                 ),uu____4908)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____4978)::uu____4979::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____5049)::
                      (uu____5050,(arg,uu____5052))::[] ->
                      maybe_auto_squash arg
                  | (uu____5125,(p,uu____5127))::(uu____5128,(q,uu____5130))::[]
                      ->
                      let uu____5202 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____5202
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____5207 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____5225 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____5225
                   then
                     let uu____5228 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____5228 with
                     | (FStar_Pervasives_Native.Some (true ),uu____5286)::
                         (FStar_Pervasives_Native.Some (true ),uu____5287)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____5361)::
                         (FStar_Pervasives_Native.Some (false ),uu____5362)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____5436)::
                         (FStar_Pervasives_Native.Some (false ),uu____5437)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____5511)::
                         (FStar_Pervasives_Native.Some (true ),uu____5512)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____5586,(arg,uu____5588))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____5589)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____5662)::
                         (uu____5663,(arg,uu____5665))::[] ->
                         maybe_auto_squash arg
                     | (uu____5738,(arg,uu____5740))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____5741)::[]
                         ->
                         let uu____5814 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5814
                     | (FStar_Pervasives_Native.Some (false ),uu____5815)::
                         (uu____5816,(arg,uu____5818))::[] ->
                         let uu____5891 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____5891
                     | (uu____5892,(p,uu____5894))::(uu____5895,(q,uu____5897))::[]
                         ->
                         let uu____5969 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____5969
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____5974 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____5992 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____5992
                      then
                        let uu____5995 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____5995 with
                        | (FStar_Pervasives_Native.Some (true ),uu____6053)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____6097)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____6141 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____6159 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____6159
                         then
                           match args with
                           | (t,uu____6163)::[] ->
                               let uu____6188 =
                                 let uu____6189 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6189.FStar_Syntax_Syntax.n  in
                               (match uu____6188 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6192::[],body,uu____6194) ->
                                    let uu____6229 = simp_t body  in
                                    (match uu____6229 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____6235 -> tm)
                                | uu____6239 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____6241))::
                               (t,uu____6243)::[] ->
                               let uu____6283 =
                                 let uu____6284 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____6284.FStar_Syntax_Syntax.n  in
                               (match uu____6283 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____6287::[],body,uu____6289) ->
                                    let uu____6324 = simp_t body  in
                                    (match uu____6324 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____6332 -> tm)
                                | uu____6336 -> tm)
                           | uu____6337 -> tm
                         else
                           (let uu____6350 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____6350
                            then
                              match args with
                              | (t,uu____6354)::[] ->
                                  let uu____6379 =
                                    let uu____6380 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6380.FStar_Syntax_Syntax.n  in
                                  (match uu____6379 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6383::[],body,uu____6385) ->
                                       let uu____6420 = simp_t body  in
                                       (match uu____6420 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____6426 -> tm)
                                   | uu____6430 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____6432))::
                                  (t,uu____6434)::[] ->
                                  let uu____6474 =
                                    let uu____6475 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____6475.FStar_Syntax_Syntax.n  in
                                  (match uu____6474 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____6478::[],body,uu____6480) ->
                                       let uu____6515 = simp_t body  in
                                       (match uu____6515 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____6523 -> tm)
                                   | uu____6527 -> tm)
                              | uu____6528 -> tm
                            else
                              (let uu____6541 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____6541
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____6544;
                                      FStar_Syntax_Syntax.vars = uu____6545;_},uu____6546)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____6572;
                                      FStar_Syntax_Syntax.vars = uu____6573;_},uu____6574)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____6600 -> tm
                               else
                                 (let uu____6613 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____6613
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____6627 =
                                        let uu____6628 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____6628.FStar_Syntax_Syntax.n  in
                                      match uu____6627 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____6639 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____6653 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____6653
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____6692 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____6692
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____6698 =
                                             let uu____6699 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____6699.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6698 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____6702 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____6710 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____6710
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____6719 =
                                                      let uu____6720 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____6720.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____6719 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____6726) ->
                                                        hd1
                                                    | uu____6751 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____6755 =
                                                    let uu____6766 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____6766]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____6755)
                                           | uu____6799 -> tm))
                                     else tm)
                                  else
                                    (let uu____6804 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____6804
                                     then
                                       match args with
                                       | (_typ,uu____6808)::(a1,uu____6810)::
                                           (a2,uu____6812)::[] ->
                                           let uu____6869 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____6869 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____6870 -> tm)
                                       | uu____6871 -> tm
                                     else
                                       (let uu____6884 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____6884
                                        then
                                          match args with
                                          | (t1,uu____6888)::(t2,uu____6890)::
                                              (a1,uu____6892)::(a2,uu____6894)::[]
                                              ->
                                              let uu____6967 =
                                                let uu____6968 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____6969 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____6968 uu____6969
                                                 in
                                              (match uu____6967 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____6970 -> tm)
                                          | uu____6971 -> tm
                                        else
                                          (let uu____6984 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____6984 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____7004 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____7014;
             FStar_Syntax_Syntax.vars = uu____7015;_},args)
          ->
          let uu____7041 =
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid  in
          if uu____7041
          then
            let uu____7044 =
              FStar_All.pipe_right args (FStar_List.map simplify1)  in
            (match uu____7044 with
             | (FStar_Pervasives_Native.Some (true ),uu____7102)::(uu____7103,
                                                                   (arg,uu____7105))::[]
                 -> maybe_auto_squash arg
             | (uu____7178,(arg,uu____7180))::(FStar_Pervasives_Native.Some
                                               (true ),uu____7181)::[]
                 -> maybe_auto_squash arg
             | (FStar_Pervasives_Native.Some (false ),uu____7254)::uu____7255::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7325::(FStar_Pervasives_Native.Some (false ),uu____7326)::[]
                 -> w FStar_Syntax_Util.t_false
             | uu____7396 -> squashed_head_un_auto_squash_args tm)
          else
            (let uu____7414 =
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid  in
             if uu____7414
             then
               let uu____7417 =
                 FStar_All.pipe_right args (FStar_List.map simplify1)  in
               match uu____7417 with
               | (FStar_Pervasives_Native.Some (true ),uu____7475)::uu____7476::[]
                   -> w FStar_Syntax_Util.t_true
               | uu____7546::(FStar_Pervasives_Native.Some (true
                              ),uu____7547)::[]
                   -> w FStar_Syntax_Util.t_true
               | (FStar_Pervasives_Native.Some (false ),uu____7617)::
                   (uu____7618,(arg,uu____7620))::[] -> maybe_auto_squash arg
               | (uu____7693,(arg,uu____7695))::(FStar_Pervasives_Native.Some
                                                 (false ),uu____7696)::[]
                   -> maybe_auto_squash arg
               | uu____7769 -> squashed_head_un_auto_squash_args tm
             else
               (let uu____7787 =
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                   in
                if uu____7787
                then
                  let uu____7790 =
                    FStar_All.pipe_right args (FStar_List.map simplify1)  in
                  match uu____7790 with
                  | uu____7848::(FStar_Pervasives_Native.Some (true
                                 ),uu____7849)::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (false ),uu____7919)::uu____7920::[]
                      -> w FStar_Syntax_Util.t_true
                  | (FStar_Pervasives_Native.Some (true ),uu____7990)::
                      (uu____7991,(arg,uu____7993))::[] ->
                      maybe_auto_squash arg
                  | (uu____8066,(p,uu____8068))::(uu____8069,(q,uu____8071))::[]
                      ->
                      let uu____8143 = FStar_Syntax_Util.term_eq p q  in
                      (if uu____8143
                       then w FStar_Syntax_Util.t_true
                       else squashed_head_un_auto_squash_args tm)
                  | uu____8148 -> squashed_head_un_auto_squash_args tm
                else
                  (let uu____8166 =
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.iff_lid
                      in
                   if uu____8166
                   then
                     let uu____8169 =
                       FStar_All.pipe_right args (FStar_List.map simplify1)
                        in
                     match uu____8169 with
                     | (FStar_Pervasives_Native.Some (true ),uu____8227)::
                         (FStar_Pervasives_Native.Some (true ),uu____8228)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (false ),uu____8302)::
                         (FStar_Pervasives_Native.Some (false ),uu____8303)::[]
                         -> w FStar_Syntax_Util.t_true
                     | (FStar_Pervasives_Native.Some (true ),uu____8377)::
                         (FStar_Pervasives_Native.Some (false ),uu____8378)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (FStar_Pervasives_Native.Some (false ),uu____8452)::
                         (FStar_Pervasives_Native.Some (true ),uu____8453)::[]
                         -> w FStar_Syntax_Util.t_false
                     | (uu____8527,(arg,uu____8529))::(FStar_Pervasives_Native.Some
                                                       (true ),uu____8530)::[]
                         -> maybe_auto_squash arg
                     | (FStar_Pervasives_Native.Some (true ),uu____8603)::
                         (uu____8604,(arg,uu____8606))::[] ->
                         maybe_auto_squash arg
                     | (uu____8679,(arg,uu____8681))::(FStar_Pervasives_Native.Some
                                                       (false ),uu____8682)::[]
                         ->
                         let uu____8755 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8755
                     | (FStar_Pervasives_Native.Some (false ),uu____8756)::
                         (uu____8757,(arg,uu____8759))::[] ->
                         let uu____8832 = FStar_Syntax_Util.mk_neg arg  in
                         maybe_auto_squash uu____8832
                     | (uu____8833,(p,uu____8835))::(uu____8836,(q,uu____8838))::[]
                         ->
                         let uu____8910 = FStar_Syntax_Util.term_eq p q  in
                         (if uu____8910
                          then w FStar_Syntax_Util.t_true
                          else squashed_head_un_auto_squash_args tm)
                     | uu____8915 -> squashed_head_un_auto_squash_args tm
                   else
                     (let uu____8933 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.not_lid
                         in
                      if uu____8933
                      then
                        let uu____8936 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        match uu____8936 with
                        | (FStar_Pervasives_Native.Some (true ),uu____8994)::[]
                            -> w FStar_Syntax_Util.t_false
                        | (FStar_Pervasives_Native.Some (false ),uu____9038)::[]
                            -> w FStar_Syntax_Util.t_true
                        | uu____9082 -> squashed_head_un_auto_squash_args tm
                      else
                        (let uu____9100 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.forall_lid
                            in
                         if uu____9100
                         then
                           match args with
                           | (t,uu____9104)::[] ->
                               let uu____9129 =
                                 let uu____9130 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9130.FStar_Syntax_Syntax.n  in
                               (match uu____9129 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9133::[],body,uu____9135) ->
                                    let uu____9170 = simp_t body  in
                                    (match uu____9170 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | uu____9176 -> tm)
                                | uu____9180 -> tm)
                           | (ty,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9182))::
                               (t,uu____9184)::[] ->
                               let uu____9224 =
                                 let uu____9225 =
                                   FStar_Syntax_Subst.compress t  in
                                 uu____9225.FStar_Syntax_Syntax.n  in
                               (match uu____9224 with
                                | FStar_Syntax_Syntax.Tm_abs
                                    (uu____9228::[],body,uu____9230) ->
                                    let uu____9265 = simp_t body  in
                                    (match uu____9265 with
                                     | FStar_Pervasives_Native.Some (true )
                                         -> w FStar_Syntax_Util.t_true
                                     | FStar_Pervasives_Native.Some (false )
                                         when clearly_inhabited ty ->
                                         w FStar_Syntax_Util.t_false
                                     | uu____9273 -> tm)
                                | uu____9277 -> tm)
                           | uu____9278 -> tm
                         else
                           (let uu____9291 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.exists_lid
                               in
                            if uu____9291
                            then
                              match args with
                              | (t,uu____9295)::[] ->
                                  let uu____9320 =
                                    let uu____9321 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9321.FStar_Syntax_Syntax.n  in
                                  (match uu____9320 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9324::[],body,uu____9326) ->
                                       let uu____9361 = simp_t body  in
                                       (match uu____9361 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | uu____9367 -> tm)
                                   | uu____9371 -> tm)
                              | (ty,FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu____9373))::
                                  (t,uu____9375)::[] ->
                                  let uu____9415 =
                                    let uu____9416 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____9416.FStar_Syntax_Syntax.n  in
                                  (match uu____9415 with
                                   | FStar_Syntax_Syntax.Tm_abs
                                       (uu____9419::[],body,uu____9421) ->
                                       let uu____9456 = simp_t body  in
                                       (match uu____9456 with
                                        | FStar_Pervasives_Native.Some (false
                                            ) -> w FStar_Syntax_Util.t_false
                                        | FStar_Pervasives_Native.Some (true
                                            ) when clearly_inhabited ty ->
                                            w FStar_Syntax_Util.t_true
                                        | uu____9464 -> tm)
                                   | uu____9468 -> tm)
                              | uu____9469 -> tm
                            else
                              (let uu____9482 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.b2t_lid
                                  in
                               if uu____9482
                               then
                                 match args with
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (true ));
                                      FStar_Syntax_Syntax.pos = uu____9485;
                                      FStar_Syntax_Syntax.vars = uu____9486;_},uu____9487)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_bool (false ));
                                      FStar_Syntax_Syntax.pos = uu____9513;
                                      FStar_Syntax_Syntax.vars = uu____9514;_},uu____9515)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | uu____9541 -> tm
                               else
                                 (let uu____9554 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.haseq_lid
                                     in
                                  if uu____9554
                                  then
                                    let t_has_eq_for_sure t =
                                      let haseq_lids =
                                        [FStar_Parser_Const.int_lid;
                                        FStar_Parser_Const.bool_lid;
                                        FStar_Parser_Const.unit_lid;
                                        FStar_Parser_Const.string_lid]  in
                                      let uu____9568 =
                                        let uu____9569 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____9569.FStar_Syntax_Syntax.n  in
                                      match uu____9568 with
                                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                          FStar_All.pipe_right haseq_lids
                                            (FStar_List.existsb
                                               (fun l  ->
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv1 l))
                                          -> true
                                      | uu____9580 -> false  in
                                    (if
                                       (FStar_List.length args) =
                                         Prims.int_one
                                     then
                                       let t =
                                         let uu____9594 =
                                           FStar_All.pipe_right args
                                             FStar_List.hd
                                            in
                                         FStar_All.pipe_right uu____9594
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____9629 =
                                         FStar_All.pipe_right t
                                           t_has_eq_for_sure
                                          in
                                       (if uu____9629
                                        then w FStar_Syntax_Util.t_true
                                        else
                                          (let uu____9635 =
                                             let uu____9636 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____9636.FStar_Syntax_Syntax.n
                                              in
                                           match uu____9635 with
                                           | FStar_Syntax_Syntax.Tm_refine
                                               uu____9639 ->
                                               let t1 =
                                                 FStar_Syntax_Util.unrefine t
                                                  in
                                               let uu____9647 =
                                                 FStar_All.pipe_right t1
                                                   t_has_eq_for_sure
                                                  in
                                               if uu____9647
                                               then
                                                 w FStar_Syntax_Util.t_true
                                               else
                                                 (let haseq_tm =
                                                    let uu____9656 =
                                                      let uu____9657 =
                                                        FStar_Syntax_Subst.compress
                                                          tm
                                                         in
                                                      uu____9657.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____9656 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (hd1,uu____9663) ->
                                                        hd1
                                                    | uu____9688 ->
                                                        failwith
                                                          "Impossible! We have already checked that this is a Tm_app"
                                                     in
                                                  let uu____9692 =
                                                    let uu____9703 =
                                                      FStar_All.pipe_right t1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____9703]  in
                                                  FStar_Syntax_Util.mk_app
                                                    haseq_tm uu____9692)
                                           | uu____9736 -> tm))
                                     else tm)
                                  else
                                    (let uu____9741 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.eq2_lid
                                        in
                                     if uu____9741
                                     then
                                       match args with
                                       | (_typ,uu____9745)::(a1,uu____9747)::
                                           (a2,uu____9749)::[] ->
                                           let uu____9806 =
                                             FStar_Syntax_Util.eq_tm a1 a2
                                              in
                                           (match uu____9806 with
                                            | FStar_Syntax_Util.Equal  ->
                                                w FStar_Syntax_Util.t_true
                                            | FStar_Syntax_Util.NotEqual  ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9807 -> tm)
                                       | uu____9808 -> tm
                                     else
                                       (let uu____9821 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.eq3_lid
                                           in
                                        if uu____9821
                                        then
                                          match args with
                                          | (t1,uu____9825)::(t2,uu____9827)::
                                              (a1,uu____9829)::(a2,uu____9831)::[]
                                              ->
                                              let uu____9904 =
                                                let uu____9905 =
                                                  FStar_Syntax_Util.eq_tm t1
                                                    t2
                                                   in
                                                let uu____9906 =
                                                  FStar_Syntax_Util.eq_tm a1
                                                    a2
                                                   in
                                                FStar_Syntax_Util.eq_inj
                                                  uu____9905 uu____9906
                                                 in
                                              (match uu____9904 with
                                               | FStar_Syntax_Util.Equal  ->
                                                   w FStar_Syntax_Util.t_true
                                               | FStar_Syntax_Util.NotEqual 
                                                   ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____9907 -> tm)
                                          | uu____9908 -> tm
                                        else
                                          (let uu____9921 =
                                             FStar_Syntax_Util.is_auto_squash
                                               tm
                                              in
                                           match uu____9921 with
                                           | FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Syntax.U_zero
                                                ,t)
                                               when
                                               FStar_Syntax_Util.is_sub_singleton
                                                 t
                                               -> t
                                           | uu____9941 -> tm)))))))))))
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let uu____9956 = simp_t t  in
          (match uu____9956 with
           | FStar_Pervasives_Native.Some (true ) ->
               bv.FStar_Syntax_Syntax.sort
           | FStar_Pervasives_Native.Some (false ) -> tm
           | FStar_Pervasives_Native.None  -> tm)
      | FStar_Syntax_Syntax.Tm_match uu____9965 ->
          let uu____9988 = is_const_match tm  in
          (match uu____9988 with
           | FStar_Pervasives_Native.Some (true ) ->
               w FStar_Syntax_Util.t_true
           | FStar_Pervasives_Native.Some (false ) ->
               w FStar_Syntax_Util.t_false
           | FStar_Pervasives_Native.None  -> tm)
      | uu____9997 -> tm
  