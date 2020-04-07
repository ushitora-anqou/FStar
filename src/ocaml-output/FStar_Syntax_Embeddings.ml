open Prims
type norm_cb =
  (FStar_Ident.lid,FStar_Syntax_Syntax.term) FStar_Util.either ->
    FStar_Syntax_Syntax.term
let (id_norm_cb : norm_cb) =
  fun uu___0_16  ->
    match uu___0_16 with
    | FStar_Util.Inr x -> x
    | FStar_Util.Inl l ->
        let uu____23 =
          FStar_Syntax_Syntax.lid_as_fv l
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____23
  
exception Embedding_failure 
let (uu___is_Embedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embedding_failure  -> true | uu____33 -> false
  
exception Unembedding_failure 
let (uu___is_Unembedding_failure : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unembedding_failure  -> true | uu____44 -> false
  
type shadow_term =
  FStar_Syntax_Syntax.term FStar_Thunk.t FStar_Pervasives_Native.option
let (map_shadow :
  shadow_term ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> shadow_term)
  = fun s  -> fun f  -> FStar_Util.map_opt s (FStar_Thunk.map f) 
let (force_shadow :
  shadow_term -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun s  -> FStar_Util.map_opt s FStar_Thunk.force 
type embed_t =
  FStar_Range.range -> shadow_term -> norm_cb -> FStar_Syntax_Syntax.term
type 'a unembed_t =
  Prims.bool -> norm_cb -> 'a FStar_Pervasives_Native.option
type 'a raw_embedder = 'a -> embed_t
type 'a raw_unembedder = FStar_Syntax_Syntax.term -> 'a unembed_t
type 'a printer = 'a -> Prims.string
type 'a embedding =
  {
  em: 'a -> embed_t ;
  un: FStar_Syntax_Syntax.term -> 'a unembed_t ;
  typ: FStar_Syntax_Syntax.typ ;
  print: 'a printer ;
  emb_typ: FStar_Syntax_Syntax.emb_typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> 'a -> embed_t =
  fun projectee  ->
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun projectee  ->
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> un
  
let __proj__Mkembedding__item__typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with | { em; un; typ; print = print7; emb_typ;_} -> typ
  
let __proj__Mkembedding__item__print : 'a . 'a embedding -> 'a printer =
  fun projectee  ->
    match projectee with
    | { em; un; typ; print = print7; emb_typ;_} -> print7
  
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee  ->
    match projectee with
    | { em; un; typ; print = print7; emb_typ;_} -> emb_typ
  
let emb_typ_of : 'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun e  -> e.emb_typ 
let unknown_printer :
  'Auu____457 . FStar_Syntax_Syntax.term -> 'Auu____457 -> Prims.string =
  fun typ  ->
    fun uu____468  ->
      let uu____469 = FStar_Syntax_Print.term_to_string typ  in
      FStar_Util.format1 "unknown %s" uu____469
  
let (term_as_fv : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.fv) =
  fun t  ->
    let uu____478 =
      let uu____479 = FStar_Syntax_Subst.compress t  in
      uu____479.FStar_Syntax_Syntax.n  in
    match uu____478 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv
    | uu____483 ->
        let uu____484 =
          let uu____486 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "Embeddings not defined for type %s" uu____486
           in
        failwith uu____484
  
let mk_emb :
  'a .
    'a raw_embedder ->
      'a raw_unembedder -> FStar_Syntax_Syntax.fv -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun fv  ->
        let typ = FStar_Syntax_Syntax.fv_to_tm fv  in
        let uu____529 =
          let uu____530 =
            let uu____538 =
              let uu____540 = FStar_Syntax_Syntax.lid_of_fv fv  in
              FStar_All.pipe_right uu____540 FStar_Ident.string_of_lid  in
            (uu____538, [])  in
          FStar_Syntax_Syntax.ET_app uu____530  in
        { em; un; typ; print = (unknown_printer typ); emb_typ = uu____529 }
  
let mk_emb_full :
  'a .
    'a raw_embedder ->
      'a raw_unembedder ->
        FStar_Syntax_Syntax.typ ->
          ('a -> Prims.string) -> FStar_Syntax_Syntax.emb_typ -> 'a embedding
  =
  fun em  ->
    fun un  ->
      fun typ  ->
        fun printer  ->
          fun emb_typ  -> { em; un; typ; print = printer; emb_typ }
  
let embed : 'a . 'a embedding -> 'a -> embed_t = fun e  -> fun x  -> e.em x 
let unembed : 'a . 'a embedding -> FStar_Syntax_Syntax.term -> 'a unembed_t =
  fun e  -> fun t  -> e.un t 
let warn_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____689 = unembed e t  in uu____689 true n1
  
let try_unembed :
  'a .
    'a embedding ->
      FStar_Syntax_Syntax.term ->
        norm_cb -> 'a FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  -> fun n1  -> let uu____730 = unembed e t  in uu____730 false n1
  
let type_of : 'a . 'a embedding -> FStar_Syntax_Syntax.typ = fun e  -> e.typ 
let set_type : 'a . FStar_Syntax_Syntax.typ -> 'a embedding -> 'a embedding =
  fun ty  ->
    fun e  ->
      let uu___77_777 = e  in
      {
        em = (uu___77_777.em);
        un = (uu___77_777.un);
        typ = ty;
        print = (uu___77_777.print);
        emb_typ = (uu___77_777.emb_typ)
      }
  
let lazy_embed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Range.range ->
          FStar_Syntax_Syntax.term ->
            'a ->
              (unit -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun pa  ->
    fun et  ->
      fun rng  ->
        fun ta  ->
          fun x  ->
            fun f  ->
              (let uu____840 = FStar_ST.op_Bang FStar_Options.debug_embedding
                  in
               if uu____840
               then
                 let uu____864 = FStar_Syntax_Print.term_to_string ta  in
                 let uu____866 = FStar_Syntax_Print.emb_typ_to_string et  in
                 let uu____868 = pa x  in
                 FStar_Util.print3
                   "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____864
                   uu____866 uu____868
               else ());
              (let uu____873 = FStar_ST.op_Bang FStar_Options.eager_embedding
                  in
               if uu____873
               then f ()
               else
                 (let thunk1 = FStar_Thunk.mk f  in
                  let uu____908 =
                    let uu____909 =
                      let uu____910 = FStar_Dyn.mkdyn x  in
                      {
                        FStar_Syntax_Syntax.blob = uu____910;
                        FStar_Syntax_Syntax.lkind =
                          (FStar_Syntax_Syntax.Lazy_embedding (et, thunk1));
                        FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun;
                        FStar_Syntax_Syntax.rng = rng
                      }  in
                    FStar_Syntax_Syntax.Tm_lazy uu____909  in
                  FStar_Syntax_Syntax.mk uu____908 rng))
  
let lazy_unembed :
  'a .
    'a printer ->
      FStar_Syntax_Syntax.emb_typ ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun pa  ->
    fun et  ->
      fun x  ->
        fun ta  ->
          fun f  ->
            let x1 = FStar_Syntax_Subst.compress x  in
            match x1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_lazy
                { FStar_Syntax_Syntax.blob = b;
                  FStar_Syntax_Syntax.lkind =
                    FStar_Syntax_Syntax.Lazy_embedding (et',t);
                  FStar_Syntax_Syntax.ltyp = uu____977;
                  FStar_Syntax_Syntax.rng = uu____978;_}
                ->
                let uu____989 =
                  (et <> et') ||
                    (FStar_ST.op_Bang FStar_Options.eager_embedding)
                   in
                if uu____989
                then
                  let res =
                    let uu____1018 = FStar_Thunk.force t  in f uu____1018  in
                  ((let uu____1022 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1022
                    then
                      let uu____1046 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1048 =
                        FStar_Syntax_Print.emb_typ_to_string et'  in
                      let uu____1050 =
                        match res with
                        | FStar_Pervasives_Native.None  -> "None"
                        | FStar_Pervasives_Native.Some x2 ->
                            let uu____1055 = pa x2  in
                            Prims.op_Hat "Some " uu____1055
                         in
                      FStar_Util.print3
                        "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n"
                        uu____1046 uu____1048 uu____1050
                    else ());
                   res)
                else
                  (let a = FStar_Dyn.undyn b  in
                   (let uu____1065 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____1065
                    then
                      let uu____1089 =
                        FStar_Syntax_Print.emb_typ_to_string et  in
                      let uu____1091 = pa a  in
                      FStar_Util.print2
                        "Unembed cancelled for %s\n\tvalue is %s\n"
                        uu____1089 uu____1091
                    else ());
                   FStar_Pervasives_Native.Some a)
            | uu____1096 ->
                let aopt = f x1  in
                ((let uu____1101 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____1101
                  then
                    let uu____1125 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____1127 = FStar_Syntax_Print.term_to_string x1  in
                    let uu____1129 =
                      match aopt with
                      | FStar_Pervasives_Native.None  -> "None"
                      | FStar_Pervasives_Native.Some a ->
                          let uu____1134 = pa a  in
                          Prims.op_Hat "Some " uu____1134
                       in
                    FStar_Util.print3
                      "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n"
                      uu____1125 uu____1127 uu____1129
                  else ());
                 aopt)
  
let (mk_any_emb :
  FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term embedding) =
  fun typ  ->
    let em t _r _topt _norm =
      (let uu____1172 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1172
       then
         let uu____1196 = unknown_printer typ t  in
         FStar_Util.print1 "Embedding abstract: %s\n" uu____1196
       else ());
      t  in
    let un t _w _n =
      (let uu____1224 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____1224
       then
         let uu____1248 = unknown_printer typ t  in
         FStar_Util.print1 "Unembedding abstract: %s\n" uu____1248
       else ());
      FStar_Pervasives_Native.Some t  in
    mk_emb_full em un typ (unknown_printer typ)
      FStar_Syntax_Syntax.ET_abstract
  
let (e_any : FStar_Syntax_Syntax.term embedding) =
  let em t _r _topt _norm = t  in
  let un t _w _n = FStar_Pervasives_Native.Some t  in
  let uu____1301 =
    let uu____1302 =
      let uu____1310 =
        FStar_All.pipe_right FStar_Parser_Const.term_lid
          FStar_Ident.string_of_lid
         in
      (uu____1310, [])  in
    FStar_Syntax_Syntax.ET_app uu____1302  in
  mk_emb_full em un FStar_Syntax_Syntax.t_term
    FStar_Syntax_Print.term_to_string uu____1301
  
let (e_unit : unit embedding) =
  let em u rng _topt _norm =
    let uu___151_1342 = FStar_Syntax_Util.exp_unit  in
    {
      FStar_Syntax_Syntax.n = (uu___151_1342.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___151_1342.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unascribe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit ) ->
        FStar_Pervasives_Native.Some ()
    | uu____1370 ->
        (if w
         then
           (let uu____1373 =
              let uu____1379 =
                let uu____1381 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1 "Not an embedded unit: %s" uu____1381  in
              (FStar_Errors.Warning_NotEmbedded, uu____1379)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1373)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____1387 =
    let uu____1388 =
      let uu____1396 =
        FStar_All.pipe_right FStar_Parser_Const.unit_lid
          FStar_Ident.string_of_lid
         in
      (uu____1396, [])  in
    FStar_Syntax_Syntax.ET_app uu____1388  in
  mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____1403  -> "()")
    uu____1387
  
let (e_bool : Prims.bool embedding) =
  let em b rng _topt _norm =
    let t =
      if b
      then FStar_Syntax_Util.exp_true_bool
      else FStar_Syntax_Util.exp_false_bool  in
    let uu___171_1442 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___171_1442.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___171_1442.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool b) ->
        FStar_Pervasives_Native.Some b
    | uu____1478 ->
        (if w
         then
           (let uu____1481 =
              let uu____1487 =
                let uu____1489 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded bool: %s" uu____1489  in
              (FStar_Errors.Warning_NotEmbedded, uu____1487)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1481)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____1496 =
    let uu____1497 =
      let uu____1505 =
        FStar_All.pipe_right FStar_Parser_Const.bool_lid
          FStar_Ident.string_of_lid
         in
      (uu____1505, [])  in
    FStar_Syntax_Syntax.ET_app uu____1497  in
  mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool
    uu____1496
  
let (e_char : FStar_Char.char embedding) =
  let em c rng _topt _norm =
    let t = FStar_Syntax_Util.exp_char c  in
    let uu___190_1542 = t  in
    {
      FStar_Syntax_Syntax.n = (uu___190_1542.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = rng;
      FStar_Syntax_Syntax.vars = (uu___190_1542.FStar_Syntax_Syntax.vars)
    }  in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c) ->
        FStar_Pervasives_Native.Some c
    | uu____1576 ->
        (if w
         then
           (let uu____1579 =
              let uu____1585 =
                let uu____1587 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded char: %s" uu____1587  in
              (FStar_Errors.Warning_NotEmbedded, uu____1585)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1579)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____1594 =
    let uu____1595 =
      let uu____1603 =
        FStar_All.pipe_right FStar_Parser_Const.char_lid
          FStar_Ident.string_of_lid
         in
      (uu____1603, [])  in
    FStar_Syntax_Syntax.ET_app uu____1595  in
  mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char
    uu____1594
  
let (e_int : FStar_BigInt.t embedding) =
  let t_int1 = FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid  in
  let emb_t_int =
    let uu____1615 =
      let uu____1623 =
        FStar_All.pipe_right FStar_Parser_Const.int_lid
          FStar_Ident.string_of_lid
         in
      (uu____1623, [])  in
    FStar_Syntax_Syntax.ET_app uu____1615  in
  let em i rng _topt _norm =
    lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i
      (fun uu____1654  ->
         let uu____1655 = FStar_BigInt.string_of_big_int i  in
         FStar_Syntax_Util.exp_int uu____1655)
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1
      (fun t1  ->
         match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
             (s,uu____1690)) ->
             let uu____1705 = FStar_BigInt.big_int_of_string s  in
             FStar_Pervasives_Native.Some uu____1705
         | uu____1706 ->
             (if w
              then
                (let uu____1709 =
                   let uu____1715 =
                     let uu____1717 = FStar_Syntax_Print.term_to_string t0
                        in
                     FStar_Util.format1 "Not an embedded int: %s" uu____1717
                      in
                   (FStar_Errors.Warning_NotEmbedded, uu____1715)  in
                 FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1709)
              else ();
              FStar_Pervasives_Native.None))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int
    emb_t_int
  
let (e_string : Prims.string embedding) =
  let emb_t_string =
    let uu____1728 =
      let uu____1736 =
        FStar_All.pipe_right FStar_Parser_Const.string_lid
          FStar_Ident.string_of_lid
         in
      (uu____1736, [])  in
    FStar_Syntax_Syntax.ET_app uu____1728  in
  let em s rng _topt _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, rng)))
      rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
        (s,uu____1799)) -> FStar_Pervasives_Native.Some s
    | uu____1803 ->
        (if w
         then
           (let uu____1806 =
              let uu____1812 =
                let uu____1814 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded string: %s" uu____1814
                 in
              (FStar_Errors.Warning_NotEmbedded, uu____1812)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1806)
         else ();
         FStar_Pervasives_Native.None)
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_string
    (fun x  -> Prims.op_Hat "\"" (Prims.op_Hat x "\"")) emb_t_string
  
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let t_option_a =
      let t_opt = FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid
         in
      let uu____1848 =
        let uu____1849 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____1849]
         in
      FStar_Syntax_Syntax.mk_Tm_app t_opt uu____1848 FStar_Range.dummyRange
       in
    let emb_t_option_a =
      let uu____1875 =
        let uu____1883 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____1883, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____1875  in
    let printer uu___1_1897 =
      match uu___1_1897 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____1903 =
            let uu____1905 = ea.print x  in Prims.op_Hat uu____1905 ")"  in
          Prims.op_Hat "(Some " uu____1903
       in
    let em o rng topt norm1 =
      lazy_embed printer emb_t_option_a rng t_option_a o
        (fun uu____1941  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____1942 =
                 let uu____1943 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.none_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____1943
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let uu____1944 =
                 let uu____1945 =
                   let uu____1954 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____1954  in
                 [uu____1945]  in
               FStar_Syntax_Syntax.mk_Tm_app uu____1942 uu____1944 rng
           | FStar_Pervasives_Native.Some a ->
               let shadow_a =
                 map_shadow topt
                   (fun t  ->
                      let v1 = FStar_Ident.mk_ident ("v", rng)  in
                      let some_v =
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          FStar_Parser_Const.some_lid v1
                         in
                      let some_v_tm =
                        let uu____1985 =
                          FStar_Syntax_Syntax.lid_as_fv some_v
                            FStar_Syntax_Syntax.delta_equational
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Syntax.fv_to_tm uu____1985  in
                      let uu____1986 =
                        FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                          [FStar_Syntax_Syntax.U_zero]
                         in
                      let uu____1987 =
                        let uu____1988 =
                          let uu____1997 = type_of ea  in
                          FStar_Syntax_Syntax.iarg uu____1997  in
                        let uu____1998 =
                          let uu____2009 = FStar_Syntax_Syntax.as_arg t  in
                          [uu____2009]  in
                        uu____1988 :: uu____1998  in
                      FStar_Syntax_Syntax.mk_Tm_app uu____1986 uu____1987 rng)
                  in
               let uu____2042 =
                 let uu____2043 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.some_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____2043
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let uu____2044 =
                 let uu____2045 =
                   let uu____2054 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____2054  in
                 let uu____2055 =
                   let uu____2066 =
                     let uu____2075 =
                       let uu____2076 = embed ea a  in
                       uu____2076 rng shadow_a norm1  in
                     FStar_Syntax_Syntax.as_arg uu____2075  in
                   [uu____2066]  in
                 uu____2045 :: uu____2055  in
               FStar_Syntax_Syntax.mk_Tm_app uu____2042 uu____2044 rng)
       in
    let un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_option_a t t_option_a
        (fun t1  ->
           let uu____2146 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____2146 with
           | (hd1,args) ->
               let uu____2187 =
                 let uu____2202 =
                   let uu____2203 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____2203.FStar_Syntax_Syntax.n  in
                 (uu____2202, args)  in
               (match uu____2187 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2221) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.none_lid
                    ->
                    FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,uu____2245::(a,uu____2247)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.some_lid
                    ->
                    let uu____2298 =
                      let uu____2301 = unembed ea a  in uu____2301 w norm1
                       in
                    FStar_Util.bind_opt uu____2298
                      (fun a1  ->
                         FStar_Pervasives_Native.Some
                           (FStar_Pervasives_Native.Some a1))
                | uu____2314 ->
                    (if w
                     then
                       (let uu____2331 =
                          let uu____2337 =
                            let uu____2339 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded option: %s"
                              uu____2339
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____2337)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____2331)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____2347 =
      let uu____2348 = type_of ea  in
      FStar_Syntax_Syntax.t_option_of uu____2348  in
    mk_emb_full em un uu____2347 printer emb_t_option_a
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_pair_a_b =
        let t_tup2 =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2  in
        let uu____2388 =
          let uu____2389 = FStar_Syntax_Syntax.as_arg ea.typ  in
          let uu____2398 =
            let uu____2409 = FStar_Syntax_Syntax.as_arg eb.typ  in
            [uu____2409]  in
          uu____2389 :: uu____2398  in
        FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____2388
          FStar_Range.dummyRange
         in
      let emb_t_pair_a_b =
        let uu____2443 =
          let uu____2451 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____2451, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____2443  in
      let printer uu____2467 =
        match uu____2467 with
        | (x,y) ->
            let uu____2475 = ea.print x  in
            let uu____2477 = eb.print y  in
            FStar_Util.format2 "(%s, %s)" uu____2475 uu____2477
         in
      let em x rng topt norm1 =
        lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x
          (fun uu____2521  ->
             let proj i ab =
               let proj_1 =
                 let uu____2536 =
                   FStar_Parser_Const.mk_tuple_data_lid (Prims.of_int (2))
                     rng
                    in
                 let uu____2538 =
                   FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun  in
                 FStar_Syntax_Util.mk_field_projector_name uu____2536
                   uu____2538 i
                  in
               let proj_1_tm =
                 let uu____2540 =
                   FStar_Syntax_Syntax.lid_as_fv proj_1
                     FStar_Syntax_Syntax.delta_equational
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____2540  in
               let uu____2541 =
                 FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let uu____2542 =
                 let uu____2543 =
                   let uu____2552 = type_of ea  in
                   FStar_Syntax_Syntax.iarg uu____2552  in
                 let uu____2553 =
                   let uu____2564 =
                     let uu____2573 = type_of eb  in
                     FStar_Syntax_Syntax.iarg uu____2573  in
                   let uu____2574 =
                     let uu____2585 = FStar_Syntax_Syntax.as_arg ab  in
                     [uu____2585]  in
                   uu____2564 :: uu____2574  in
                 uu____2543 :: uu____2553  in
               FStar_Syntax_Syntax.mk_Tm_app uu____2541 uu____2542 rng  in
             let shadow_a = map_shadow topt (proj Prims.int_one)  in
             let shadow_b = map_shadow topt (proj (Prims.of_int (2)))  in
             let uu____2630 =
               let uu____2631 =
                 FStar_Syntax_Syntax.tdataconstr
                   FStar_Parser_Const.lid_Mktuple2
                  in
               FStar_Syntax_Syntax.mk_Tm_uinst uu____2631
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                in
             let uu____2632 =
               let uu____2633 =
                 let uu____2642 = type_of ea  in
                 FStar_Syntax_Syntax.iarg uu____2642  in
               let uu____2643 =
                 let uu____2654 =
                   let uu____2663 = type_of eb  in
                   FStar_Syntax_Syntax.iarg uu____2663  in
                 let uu____2664 =
                   let uu____2675 =
                     let uu____2684 =
                       let uu____2685 =
                         embed ea (FStar_Pervasives_Native.fst x)  in
                       uu____2685 rng shadow_a norm1  in
                     FStar_Syntax_Syntax.as_arg uu____2684  in
                   let uu____2692 =
                     let uu____2703 =
                       let uu____2712 =
                         let uu____2713 =
                           embed eb (FStar_Pervasives_Native.snd x)  in
                         uu____2713 rng shadow_b norm1  in
                       FStar_Syntax_Syntax.as_arg uu____2712  in
                     [uu____2703]  in
                   uu____2675 :: uu____2692  in
                 uu____2654 :: uu____2664  in
               uu____2633 :: uu____2643  in
             FStar_Syntax_Syntax.mk_Tm_app uu____2630 uu____2632 rng)
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_pair_a_b t t_pair_a_b
          (fun t1  ->
             let uu____2811 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____2811 with
             | (hd1,args) ->
                 let uu____2854 =
                   let uu____2867 =
                     let uu____2868 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____2868.FStar_Syntax_Syntax.n  in
                   (uu____2867, args)  in
                 (match uu____2854 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____2886::uu____2887::(a,uu____2889)::(b,uu____2891)::[])
                      when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.lid_Mktuple2
                      ->
                      let uu____2950 =
                        let uu____2953 = unembed ea a  in uu____2953 w norm1
                         in
                      FStar_Util.bind_opt uu____2950
                        (fun a1  ->
                           let uu____2967 =
                             let uu____2970 = unembed eb b  in
                             uu____2970 w norm1  in
                           FStar_Util.bind_opt uu____2967
                             (fun b1  ->
                                FStar_Pervasives_Native.Some (a1, b1)))
                  | uu____2987 ->
                      (if w
                       then
                         (let uu____3002 =
                            let uu____3008 =
                              let uu____3010 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded pair: %s"
                                uu____3010
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____3008)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3002)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____3020 =
        let uu____3021 = type_of ea  in
        let uu____3022 = type_of eb  in
        FStar_Syntax_Syntax.t_tuple2_of uu____3021 uu____3022  in
      mk_emb_full em un uu____3020 printer emb_t_pair_a_b
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let t_sum_a_b =
        let t_either =
          FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid  in
        let uu____3064 =
          let uu____3065 = FStar_Syntax_Syntax.as_arg ea.typ  in
          let uu____3074 =
            let uu____3085 = FStar_Syntax_Syntax.as_arg eb.typ  in
            [uu____3085]  in
          uu____3065 :: uu____3074  in
        FStar_Syntax_Syntax.mk_Tm_app t_either uu____3064
          FStar_Range.dummyRange
         in
      let emb_t_sum_a_b =
        let uu____3119 =
          let uu____3127 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____3127, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____3119  in
      let printer s =
        match s with
        | FStar_Util.Inl a ->
            let uu____3150 = ea.print a  in
            FStar_Util.format1 "Inl %s" uu____3150
        | FStar_Util.Inr b ->
            let uu____3154 = eb.print b  in
            FStar_Util.format1 "Inr %s" uu____3154
         in
      let em s rng topt norm1 =
        lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s
          (match s with
           | FStar_Util.Inl a ->
               (fun uu____3201  ->
                  let shadow_a =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inl_lid v1
                            in
                         let some_v_tm =
                           let uu____3215 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____3215  in
                         let uu____3216 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero]
                            in
                         let uu____3217 =
                           let uu____3218 =
                             let uu____3227 = type_of ea  in
                             FStar_Syntax_Syntax.iarg uu____3227  in
                           let uu____3228 =
                             let uu____3239 =
                               let uu____3248 = type_of eb  in
                               FStar_Syntax_Syntax.iarg uu____3248  in
                             let uu____3249 =
                               let uu____3260 = FStar_Syntax_Syntax.as_arg t
                                  in
                               [uu____3260]  in
                             uu____3239 :: uu____3249  in
                           uu____3218 :: uu____3228  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3216 uu____3217
                           rng)
                     in
                  let uu____3301 =
                    let uu____3302 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inl_lid
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3302
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero]
                     in
                  let uu____3303 =
                    let uu____3304 =
                      let uu____3313 = type_of ea  in
                      FStar_Syntax_Syntax.iarg uu____3313  in
                    let uu____3314 =
                      let uu____3325 =
                        let uu____3334 = type_of eb  in
                        FStar_Syntax_Syntax.iarg uu____3334  in
                      let uu____3335 =
                        let uu____3346 =
                          let uu____3355 =
                            let uu____3356 = embed ea a  in
                            uu____3356 rng shadow_a norm1  in
                          FStar_Syntax_Syntax.as_arg uu____3355  in
                        [uu____3346]  in
                      uu____3325 :: uu____3335  in
                    uu____3304 :: uu____3314  in
                  FStar_Syntax_Syntax.mk_Tm_app uu____3301 uu____3303 rng)
           | FStar_Util.Inr b ->
               (fun uu____3396  ->
                  let shadow_b =
                    map_shadow topt
                      (fun t  ->
                         let v1 = FStar_Ident.mk_ident ("v", rng)  in
                         let some_v =
                           FStar_Syntax_Util.mk_field_projector_name_from_ident
                             FStar_Parser_Const.inr_lid v1
                            in
                         let some_v_tm =
                           let uu____3410 =
                             FStar_Syntax_Syntax.lid_as_fv some_v
                               FStar_Syntax_Syntax.delta_equational
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.fv_to_tm uu____3410  in
                         let uu____3411 =
                           FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm
                             [FStar_Syntax_Syntax.U_zero]
                            in
                         let uu____3412 =
                           let uu____3413 =
                             let uu____3422 = type_of ea  in
                             FStar_Syntax_Syntax.iarg uu____3422  in
                           let uu____3423 =
                             let uu____3434 =
                               let uu____3443 = type_of eb  in
                               FStar_Syntax_Syntax.iarg uu____3443  in
                             let uu____3444 =
                               let uu____3455 = FStar_Syntax_Syntax.as_arg t
                                  in
                               [uu____3455]  in
                             uu____3434 :: uu____3444  in
                           uu____3413 :: uu____3423  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3411 uu____3412
                           rng)
                     in
                  let uu____3496 =
                    let uu____3497 =
                      FStar_Syntax_Syntax.tdataconstr
                        FStar_Parser_Const.inr_lid
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____3497
                      [FStar_Syntax_Syntax.U_zero;
                      FStar_Syntax_Syntax.U_zero]
                     in
                  let uu____3498 =
                    let uu____3499 =
                      let uu____3508 = type_of ea  in
                      FStar_Syntax_Syntax.iarg uu____3508  in
                    let uu____3509 =
                      let uu____3520 =
                        let uu____3529 = type_of eb  in
                        FStar_Syntax_Syntax.iarg uu____3529  in
                      let uu____3530 =
                        let uu____3541 =
                          let uu____3550 =
                            let uu____3551 = embed eb b  in
                            uu____3551 rng shadow_b norm1  in
                          FStar_Syntax_Syntax.as_arg uu____3550  in
                        [uu____3541]  in
                      uu____3520 :: uu____3530  in
                    uu____3499 :: uu____3509  in
                  FStar_Syntax_Syntax.mk_Tm_app uu____3496 uu____3498 rng))
         in
      let un t0 w norm1 =
        let t = FStar_Syntax_Util.unmeta_safe t0  in
        lazy_unembed printer emb_t_sum_a_b t t_sum_a_b
          (fun t1  ->
             let uu____3639 = FStar_Syntax_Util.head_and_args' t1  in
             match uu____3639 with
             | (hd1,args) ->
                 let uu____3682 =
                   let uu____3697 =
                     let uu____3698 = FStar_Syntax_Util.un_uinst hd1  in
                     uu____3698.FStar_Syntax_Syntax.n  in
                   (uu____3697, args)  in
                 (match uu____3682 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3718::uu____3719::(a,uu____3721)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inl_lid
                      ->
                      let uu____3788 =
                        let uu____3791 = unembed ea a  in uu____3791 w norm1
                         in
                      FStar_Util.bind_opt uu____3788
                        (fun a1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,uu____3809::uu____3810::(b,uu____3812)::[]) when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.inr_lid
                      ->
                      let uu____3879 =
                        let uu____3882 = unembed eb b  in uu____3882 w norm1
                         in
                      FStar_Util.bind_opt uu____3879
                        (fun b1  ->
                           FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
                  | uu____3899 ->
                      (if w
                       then
                         (let uu____3916 =
                            let uu____3922 =
                              let uu____3924 =
                                FStar_Syntax_Print.term_to_string t0  in
                              FStar_Util.format1 "Not an embedded sum: %s"
                                uu____3924
                               in
                            (FStar_Errors.Warning_NotEmbedded, uu____3922)
                             in
                          FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                            uu____3916)
                       else ();
                       FStar_Pervasives_Native.None)))
         in
      let uu____3934 =
        let uu____3935 = type_of ea  in
        let uu____3936 = type_of eb  in
        FStar_Syntax_Syntax.t_either_of uu____3935 uu____3936  in
      mk_emb_full em un uu____3934 printer emb_t_sum_a_b
  
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let t_list_a =
      let t_list = FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid
         in
      let uu____3962 =
        let uu____3963 = FStar_Syntax_Syntax.as_arg ea.typ  in [uu____3963]
         in
      FStar_Syntax_Syntax.mk_Tm_app t_list uu____3962 FStar_Range.dummyRange
       in
    let emb_t_list_a =
      let uu____3989 =
        let uu____3997 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____3997, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____3989  in
    let printer l =
      let uu____4014 =
        let uu____4016 =
          let uu____4018 = FStar_List.map ea.print l  in
          FStar_All.pipe_right uu____4018 (FStar_String.concat "; ")  in
        Prims.op_Hat uu____4016 "]"  in
      Prims.op_Hat "[" uu____4014  in
    let rec em l rng shadow_l norm1 =
      lazy_embed printer emb_t_list_a rng t_list_a l
        (fun uu____4062  ->
           let t =
             let uu____4064 = type_of ea  in
             FStar_Syntax_Syntax.iarg uu____4064  in
           match l with
           | [] ->
               let uu____4065 =
                 let uu____4066 =
                   FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4066
                   [FStar_Syntax_Syntax.U_zero]
                  in
               FStar_Syntax_Syntax.mk_Tm_app uu____4065 [t] rng
           | hd1::tl1 ->
               let cons1 =
                 let uu____4088 =
                   FStar_Syntax_Syntax.tdataconstr
                     FStar_Parser_Const.cons_lid
                    in
                 FStar_Syntax_Syntax.mk_Tm_uinst uu____4088
                   [FStar_Syntax_Syntax.U_zero]
                  in
               let proj f cons_tm =
                 let fid = FStar_Ident.mk_ident (f, rng)  in
                 let proj =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     FStar_Parser_Const.cons_lid fid
                    in
                 let proj_tm =
                   let uu____4106 =
                     FStar_Syntax_Syntax.lid_as_fv proj
                       FStar_Syntax_Syntax.delta_equational
                       FStar_Pervasives_Native.None
                      in
                   FStar_Syntax_Syntax.fv_to_tm uu____4106  in
                 let uu____4107 =
                   FStar_Syntax_Syntax.mk_Tm_uinst proj_tm
                     [FStar_Syntax_Syntax.U_zero]
                    in
                 let uu____4108 =
                   let uu____4109 =
                     let uu____4118 = type_of ea  in
                     FStar_Syntax_Syntax.iarg uu____4118  in
                   let uu____4119 =
                     let uu____4130 = FStar_Syntax_Syntax.as_arg cons_tm  in
                     [uu____4130]  in
                   uu____4109 :: uu____4119  in
                 FStar_Syntax_Syntax.mk_Tm_app uu____4107 uu____4108 rng  in
               let shadow_hd = map_shadow shadow_l (proj "hd")  in
               let shadow_tl = map_shadow shadow_l (proj "tl")  in
               let uu____4167 =
                 let uu____4168 =
                   let uu____4179 =
                     let uu____4188 =
                       let uu____4189 = embed ea hd1  in
                       uu____4189 rng shadow_hd norm1  in
                     FStar_Syntax_Syntax.as_arg uu____4188  in
                   let uu____4196 =
                     let uu____4207 =
                       let uu____4216 = em tl1 rng shadow_tl norm1  in
                       FStar_Syntax_Syntax.as_arg uu____4216  in
                     [uu____4207]  in
                   uu____4179 :: uu____4196  in
                 t :: uu____4168  in
               FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4167 rng)
       in
    let rec un t0 w norm1 =
      let t = FStar_Syntax_Util.unmeta_safe t0  in
      lazy_unembed printer emb_t_list_a t t_list_a
        (fun t1  ->
           let uu____4288 = FStar_Syntax_Util.head_and_args' t1  in
           match uu____4288 with
           | (hd1,args) ->
               let uu____4329 =
                 let uu____4342 =
                   let uu____4343 = FStar_Syntax_Util.un_uinst hd1  in
                   uu____4343.FStar_Syntax_Syntax.n  in
                 (uu____4342, args)  in
               (match uu____4329 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4359) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.nil_lid
                    -> FStar_Pervasives_Native.Some []
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(uu____4379,FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____4380))::(hd2,FStar_Pervasives_Native.None
                                                                    )::
                   (tl1,FStar_Pervasives_Native.None )::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4422 =
                      let uu____4425 = unembed ea hd2  in uu____4425 w norm1
                       in
                    FStar_Util.bind_opt uu____4422
                      (fun hd3  ->
                         let uu____4437 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4437
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(hd2,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                            )::[])
                    when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.cons_lid
                    ->
                    let uu____4485 =
                      let uu____4488 = unembed ea hd2  in uu____4488 w norm1
                       in
                    FStar_Util.bind_opt uu____4485
                      (fun hd3  ->
                         let uu____4500 = un tl1 w norm1  in
                         FStar_Util.bind_opt uu____4500
                           (fun tl2  ->
                              FStar_Pervasives_Native.Some (hd3 :: tl2)))
                | uu____4515 ->
                    (if w
                     then
                       (let uu____4530 =
                          let uu____4536 =
                            let uu____4538 =
                              FStar_Syntax_Print.term_to_string t0  in
                            FStar_Util.format1 "Not an embedded list: %s"
                              uu____4538
                             in
                          (FStar_Errors.Warning_NotEmbedded, uu____4536)  in
                        FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                          uu____4530)
                     else ();
                     FStar_Pervasives_Native.None)))
       in
    let uu____4546 =
      let uu____4547 = type_of ea  in
      FStar_Syntax_Syntax.t_list_of uu____4547  in
    mk_emb_full em un uu____4546 printer emb_t_list_a
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
type norm_step =
  | Simpl 
  | Weak 
  | HNF 
  | Primops 
  | Delta 
  | Zeta 
  | Iota 
  | Reify 
  | UnfoldOnly of Prims.string Prims.list 
  | UnfoldFully of Prims.string Prims.list 
  | UnfoldAttr of Prims.string Prims.list 
  | NBE 
let (uu___is_Simpl : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____4590 -> false
  
let (uu___is_Weak : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____4601 -> false
  
let (uu___is_HNF : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____4612 -> false 
let (uu___is_Primops : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____4623 -> false
  
let (uu___is_Delta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____4634 -> false
  
let (uu___is_Zeta : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____4645 -> false
  
let (uu___is_Iota : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____4656 -> false
  
let (uu___is_Reify : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____4667 -> false
  
let (uu___is_UnfoldOnly : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____4682 -> false
  
let (__proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____4713 -> false
  
let (__proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : norm_step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____4744 -> false
  
let (__proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_NBE : norm_step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____4771 -> false 
let (steps_Simpl : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_simpl 
let (steps_Weak : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_weak 
let (steps_HNF : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_hnf 
let (steps_Primops : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_primops 
let (steps_Delta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_delta 
let (steps_Zeta : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_zeta 
let (steps_Iota : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_iota 
let (steps_Reify : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_reify 
let (steps_UnfoldOnly : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldFully : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly 
let (steps_UnfoldAttr : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldattr 
let (steps_NBE : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_nbe 
let (e_norm_step : norm_step embedding) =
  let t_norm_step1 =
    let uu____4789 =
      FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step"  in
    FStar_Syntax_Util.fvar_const uu____4789  in
  let emb_t_norm_step =
    let uu____4792 =
      let uu____4800 =
        FStar_All.pipe_right FStar_Parser_Const.norm_step_lid
          FStar_Ident.string_of_lid
         in
      (uu____4800, [])  in
    FStar_Syntax_Syntax.ET_app uu____4792  in
  let printer uu____4812 = "norm_step"  in
  let em n1 rng _topt norm1 =
    lazy_embed printer emb_t_norm_step rng t_norm_step1 n1
      (fun uu____4838  ->
         match n1 with
         | Simpl  -> steps_Simpl
         | Weak  -> steps_Weak
         | HNF  -> steps_HNF
         | Primops  -> steps_Primops
         | Delta  -> steps_Delta
         | Zeta  -> steps_Zeta
         | Iota  -> steps_Iota
         | NBE  -> steps_NBE
         | Reify  -> steps_Reify
         | UnfoldOnly l ->
             let uu____4843 =
               let uu____4844 =
                 let uu____4853 =
                   let uu____4854 =
                     let uu____4861 = e_list e_string  in embed uu____4861 l
                      in
                   uu____4854 rng FStar_Pervasives_Native.None norm1  in
                 FStar_Syntax_Syntax.as_arg uu____4853  in
               [uu____4844]  in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4843 rng
         | UnfoldFully l ->
             let uu____4893 =
               let uu____4894 =
                 let uu____4903 =
                   let uu____4904 =
                     let uu____4911 = e_list e_string  in embed uu____4911 l
                      in
                   uu____4904 rng FStar_Pervasives_Native.None norm1  in
                 FStar_Syntax_Syntax.as_arg uu____4903  in
               [uu____4894]  in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____4893 rng
         | UnfoldAttr l ->
             let uu____4943 =
               let uu____4944 =
                 let uu____4953 =
                   let uu____4954 =
                     let uu____4961 = e_list e_string  in embed uu____4961 l
                      in
                   uu____4954 rng FStar_Pervasives_Native.None norm1  in
                 FStar_Syntax_Syntax.as_arg uu____4953  in
               [uu____4944]  in
             FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____4943 rng)
     in
  let un t0 w norm1 =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    lazy_unembed printer emb_t_norm_step t t_norm_step1
      (fun t1  ->
         let uu____5021 = FStar_Syntax_Util.head_and_args t1  in
         match uu____5021 with
         | (hd1,args) ->
             let uu____5066 =
               let uu____5081 =
                 let uu____5082 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____5082.FStar_Syntax_Syntax.n  in
               (uu____5081, args)  in
             (match uu____5066 with
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_simpl
                  -> FStar_Pervasives_Native.Some Simpl
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_weak
                  -> FStar_Pervasives_Native.Some Weak
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_hnf
                  -> FStar_Pervasives_Native.Some HNF
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_primops
                  -> FStar_Pervasives_Native.Some Primops
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_delta
                  -> FStar_Pervasives_Native.Some Delta
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_zeta
                  -> FStar_Pervasives_Native.Some Zeta
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_iota
                  -> FStar_Pervasives_Native.Some Iota
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_nbe
                  -> FStar_Pervasives_Native.Some NBE
              | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_reify
                  -> FStar_Pervasives_Native.Some Reify
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5270)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldonly
                  ->
                  let uu____5305 =
                    let uu____5311 =
                      let uu____5321 = e_list e_string  in
                      unembed uu____5321 l  in
                    uu____5311 w norm1  in
                  FStar_Util.bind_opt uu____5305
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _5341  -> FStar_Pervasives_Native.Some _5341)
                         (UnfoldOnly ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5344)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldfully
                  ->
                  let uu____5379 =
                    let uu____5385 =
                      let uu____5395 = e_list e_string  in
                      unembed uu____5395 l  in
                    uu____5385 w norm1  in
                  FStar_Util.bind_opt uu____5379
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _5415  -> FStar_Pervasives_Native.Some _5415)
                         (UnfoldFully ss))
              | (FStar_Syntax_Syntax.Tm_fvar fv,(l,uu____5418)::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.steps_unfoldattr
                  ->
                  let uu____5453 =
                    let uu____5459 =
                      let uu____5469 = e_list e_string  in
                      unembed uu____5469 l  in
                    uu____5459 w norm1  in
                  FStar_Util.bind_opt uu____5453
                    (fun ss  ->
                       FStar_All.pipe_left
                         (fun _5489  -> FStar_Pervasives_Native.Some _5489)
                         (UnfoldAttr ss))
              | uu____5490 ->
                  (if w
                   then
                     (let uu____5507 =
                        let uu____5513 =
                          let uu____5515 =
                            FStar_Syntax_Print.term_to_string t0  in
                          FStar_Util.format1 "Not an embedded norm_step: %s"
                            uu____5515
                           in
                        (FStar_Errors.Warning_NotEmbedded, uu____5513)  in
                      FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                        uu____5507)
                   else ();
                   FStar_Pervasives_Native.None)))
     in
  mk_emb_full em un FStar_Syntax_Syntax.t_norm_step printer emb_t_norm_step 
let (e_range : FStar_Range.range embedding) =
  let em r rng _shadow _norm =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r)) rng
     in
  let un t0 w _norm =
    let t = FStar_Syntax_Util.unmeta_safe t0  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r) ->
        FStar_Pervasives_Native.Some r
    | uu____5575 ->
        (if w
         then
           (let uu____5578 =
              let uu____5584 =
                let uu____5586 = FStar_Syntax_Print.term_to_string t0  in
                FStar_Util.format1 "Not an embedded range: %s" uu____5586  in
              (FStar_Errors.Warning_NotEmbedded, uu____5584)  in
            FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5578)
         else ();
         FStar_Pervasives_Native.None)
     in
  let uu____5592 =
    let uu____5593 =
      let uu____5601 =
        FStar_All.pipe_right FStar_Parser_Const.range_lid
          FStar_Ident.string_of_lid
         in
      (uu____5601, [])  in
    FStar_Syntax_Syntax.ET_app uu____5593  in
  mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range
    uu____5592
  
let or_else : 'a . 'a FStar_Pervasives_Native.option -> (unit -> 'a) -> 'a =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Pervasives_Native.Some x -> x
      | FStar_Pervasives_Native.None  -> g ()
  
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let t_arrow =
        let uu____5672 =
          let uu____5673 =
            let uu____5688 =
              let uu____5697 =
                let uu____5704 = FStar_Syntax_Syntax.null_bv ea.typ  in
                (uu____5704, FStar_Pervasives_Native.None)  in
              [uu____5697]  in
            let uu____5719 = FStar_Syntax_Syntax.mk_Total eb.typ  in
            (uu____5688, uu____5719)  in
          FStar_Syntax_Syntax.Tm_arrow uu____5673  in
        FStar_Syntax_Syntax.mk uu____5672 FStar_Range.dummyRange  in
      let emb_t_arr_a_b =
        FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let printer f = "<fun>"  in
      let em f rng shadow_f norm1 =
        lazy_embed (fun uu____5791  -> "<fun>") emb_t_arr_a_b rng t_arrow f
          (fun uu____5797  ->
             let uu____5798 = force_shadow shadow_f  in
             match uu____5798 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Exn.raise Embedding_failure
             | FStar_Pervasives_Native.Some repr_f ->
                 ((let uu____5803 =
                     FStar_ST.op_Bang FStar_Options.debug_embedding  in
                   if uu____5803
                   then
                     let uu____5827 =
                       FStar_Syntax_Print.term_to_string repr_f  in
                     let uu____5829 = FStar_Util.stack_dump ()  in
                     FStar_Util.print2
                       "e_arrow forced back to term using shadow %s; repr=%s\n"
                       uu____5827 uu____5829
                   else ());
                  (let res = norm1 (FStar_Util.Inr repr_f)  in
                   (let uu____5836 =
                      FStar_ST.op_Bang FStar_Options.debug_embedding  in
                    if uu____5836
                    then
                      let uu____5860 =
                        FStar_Syntax_Print.term_to_string repr_f  in
                      let uu____5862 = FStar_Syntax_Print.term_to_string res
                         in
                      let uu____5864 = FStar_Util.stack_dump ()  in
                      FStar_Util.print3
                        "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n"
                        uu____5860 uu____5862 uu____5864
                    else ());
                   res)))
         in
      let un f w norm1 =
        lazy_unembed printer emb_t_arr_a_b f t_arrow
          (fun f1  ->
             let f_wrapped a =
               (let uu____5923 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____5923
                then
                  let uu____5947 = FStar_Syntax_Print.term_to_string f1  in
                  let uu____5949 = FStar_Util.stack_dump ()  in
                  FStar_Util.print2
                    "Calling back into normalizer for %s\n%s\n" uu____5947
                    uu____5949
                else ());
               (let a_tm =
                  let uu____5955 = embed ea a  in
                  uu____5955 f1.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None norm1
                   in
                let b_tm =
                  let uu____5965 =
                    let uu____5970 =
                      let uu____5971 =
                        let uu____5972 = FStar_Syntax_Syntax.as_arg a_tm  in
                        [uu____5972]  in
                      FStar_Syntax_Syntax.mk_Tm_app f1 uu____5971
                        f1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Util.Inr uu____5970  in
                  norm1 uu____5965  in
                let uu____5997 =
                  let uu____6000 = unembed eb b_tm  in uu____6000 w norm1  in
                match uu____5997 with
                | FStar_Pervasives_Native.None  ->
                    FStar_Exn.raise Unembedding_failure
                | FStar_Pervasives_Native.Some b -> b)
                in
             FStar_Pervasives_Native.Some f_wrapped)
         in
      mk_emb_full em un t_arrow printer emb_t_arr_a_b
  
let arrow_as_prim_step_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          Prims.int ->
            FStar_Ident.lid ->
              norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun f  ->
        fun n_tvars  ->
          fun fv_lid1  ->
            fun norm1  ->
              let rng = FStar_Ident.range_of_lid fv_lid1  in
              let f_wrapped args =
                let uu____6094 = FStar_List.splitAt n_tvars args  in
                match uu____6094 with
                | (_tvar_args,rest_args) ->
                    let uu____6171 = FStar_List.hd rest_args  in
                    (match uu____6171 with
                     | (x,uu____6191) ->
                         let shadow_app =
                           let uu____6205 =
                             FStar_Thunk.mk
                               (fun uu____6210  ->
                                  let uu____6211 =
                                    norm1 (FStar_Util.Inl fv_lid1)  in
                                  FStar_Syntax_Syntax.mk_Tm_app uu____6211
                                    args rng)
                              in
                           FStar_Pervasives_Native.Some uu____6205  in
                         let uu____6214 =
                           let uu____6217 =
                             let uu____6220 = unembed ea x  in
                             uu____6220 true norm1  in
                           FStar_Util.map_opt uu____6217
                             (fun x1  ->
                                let uu____6231 =
                                  let uu____6238 = f x1  in
                                  embed eb uu____6238  in
                                uu____6231 rng shadow_app norm1)
                            in
                         (match uu____6214 with
                          | FStar_Pervasives_Native.Some x1 ->
                              FStar_Pervasives_Native.Some x1
                          | FStar_Pervasives_Native.None  ->
                              force_shadow shadow_app))
                 in
              f_wrapped
  
let arrow_as_prim_step_2 :
  'a 'b 'c .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          ('a -> 'b -> 'c) ->
            Prims.int ->
              FStar_Ident.lid ->
                norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun f  ->
          fun n_tvars  ->
            fun fv_lid1  ->
              fun norm1  ->
                let rng = FStar_Ident.range_of_lid fv_lid1  in
                let f_wrapped args =
                  let uu____6341 = FStar_List.splitAt n_tvars args  in
                  match uu____6341 with
                  | (_tvar_args,rest_args) ->
                      let uu____6404 = FStar_List.hd rest_args  in
                      (match uu____6404 with
                       | (x,uu____6420) ->
                           let uu____6425 =
                             let uu____6432 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____6432  in
                           (match uu____6425 with
                            | (y,uu____6456) ->
                                let shadow_app =
                                  let uu____6466 =
                                    FStar_Thunk.mk
                                      (fun uu____6471  ->
                                         let uu____6472 =
                                           norm1 (FStar_Util.Inl fv_lid1)  in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____6472 args rng)
                                     in
                                  FStar_Pervasives_Native.Some uu____6466  in
                                let uu____6475 =
                                  let uu____6478 =
                                    let uu____6481 = unembed ea x  in
                                    uu____6481 true norm1  in
                                  FStar_Util.bind_opt uu____6478
                                    (fun x1  ->
                                       let uu____6492 =
                                         let uu____6495 = unembed eb y  in
                                         uu____6495 true norm1  in
                                       FStar_Util.bind_opt uu____6492
                                         (fun y1  ->
                                            let uu____6506 =
                                              let uu____6507 =
                                                let uu____6514 = f x1 y1  in
                                                embed ec uu____6514  in
                                              uu____6507 rng shadow_app norm1
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____6506))
                                   in
                                (match uu____6475 with
                                 | FStar_Pervasives_Native.Some x1 ->
                                     FStar_Pervasives_Native.Some x1
                                 | FStar_Pervasives_Native.None  ->
                                     force_shadow shadow_app)))
                   in
                f_wrapped
  
let arrow_as_prim_step_3 :
  'a 'b 'c 'd .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          'd embedding ->
            ('a -> 'b -> 'c -> 'd) ->
              Prims.int ->
                FStar_Ident.lid ->
                  norm_cb ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun f  ->
            fun n_tvars  ->
              fun fv_lid1  ->
                fun norm1  ->
                  let rng = FStar_Ident.range_of_lid fv_lid1  in
                  let f_wrapped args =
                    let uu____6636 = FStar_List.splitAt n_tvars args  in
                    match uu____6636 with
                    | (_tvar_args,rest_args) ->
                        let uu____6699 = FStar_List.hd rest_args  in
                        (match uu____6699 with
                         | (x,uu____6715) ->
                             let uu____6720 =
                               let uu____6727 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____6727  in
                             (match uu____6720 with
                              | (y,uu____6751) ->
                                  let uu____6756 =
                                    let uu____6763 =
                                      let uu____6772 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____6772  in
                                    FStar_List.hd uu____6763  in
                                  (match uu____6756 with
                                   | (z,uu____6802) ->
                                       let shadow_app =
                                         let uu____6812 =
                                           FStar_Thunk.mk
                                             (fun uu____6817  ->
                                                let uu____6818 =
                                                  norm1
                                                    (FStar_Util.Inl fv_lid1)
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____6818 args rng)
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6812
                                          in
                                       let uu____6821 =
                                         let uu____6824 =
                                           let uu____6827 = unembed ea x  in
                                           uu____6827 true norm1  in
                                         FStar_Util.bind_opt uu____6824
                                           (fun x1  ->
                                              let uu____6838 =
                                                let uu____6841 = unembed eb y
                                                   in
                                                uu____6841 true norm1  in
                                              FStar_Util.bind_opt uu____6838
                                                (fun y1  ->
                                                   let uu____6852 =
                                                     let uu____6855 =
                                                       unembed ec z  in
                                                     uu____6855 true norm1
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____6852
                                                     (fun z1  ->
                                                        let uu____6866 =
                                                          let uu____6867 =
                                                            let uu____6874 =
                                                              f x1 y1 z1  in
                                                            embed ed
                                                              uu____6874
                                                             in
                                                          uu____6867 rng
                                                            shadow_app norm1
                                                           in
                                                        FStar_Pervasives_Native.Some
                                                          uu____6866)))
                                          in
                                       (match uu____6821 with
                                        | FStar_Pervasives_Native.Some x1 ->
                                            FStar_Pervasives_Native.Some x1
                                        | FStar_Pervasives_Native.None  ->
                                            force_shadow shadow_app))))
                     in
                  f_wrapped
  
let debug_wrap : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s  ->
    fun f  ->
      (let uu____6904 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
       if uu____6904 then FStar_Util.print1 "++++starting %s\n" s else ());
      (let res = f ()  in
       (let uu____6933 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
        if uu____6933 then FStar_Util.print1 "------ending %s\n" s else ());
       res)
  