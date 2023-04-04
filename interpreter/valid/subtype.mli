open Etypes

val subtype_core_extern_desc : ctx -> core_extern_desc -> core_extern_desc -> unit

val subtype_val_type : ctx -> val_type -> val_type -> unit
val subtype_val_type_option : ctx -> val_type option -> val_type option -> unit
val subtype_extern_desc : ctx -> extern_desc -> extern_desc -> unit
val def_type_is_resource : ctx -> def_type -> unit
