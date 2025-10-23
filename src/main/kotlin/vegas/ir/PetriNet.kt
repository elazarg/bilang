package vegas.ir

import vegas.FieldRef

// Petri IR
data class PlaceId(val name: String)
data class TransId(val name: String)

data class Place(val id: PlaceId)

data class ArcPT(val p: PlaceId, val t: TransId)
data class ArcTP(val t: TransId, val p: PlaceId)

// Pure control net
data class PetriNet(
    val places: Set<Place>,
    val trans: Set<TransId>,
    val pre: Set<ArcPT>,   // P -> T
    val post: Set<ArcTP>   // T -> P
)

// Guards and updates attached to transitions
sealed class Guard {
    object True : Guard()
    data class ExprGuard(val e: Expr) : Guard()
}
sealed class Update { // “writes” on firing
    /** Mark a (role,param) field as defined. Value itself is supplied externally at runtime. */
    data class MarkDefined(val field: FieldRef) : Update()
    // usually a single update per role-parameter completion
}
data class TransitionAnn(
    val id: TransId,
    val guard: Guard,
    val updates: List<Update>
)

// Bundle
data class PNSystem(val net: PetriNet, val ann: Map<TransId, TransitionAnn>, val init: Set<PlaceId>)
