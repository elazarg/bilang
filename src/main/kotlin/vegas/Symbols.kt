package vegas

@JvmInline
value class RoleId(val name: String) {
    companion object {
        @JvmStatic fun of(name: String) = RoleId(name)
    }
}

@JvmInline
value class VarId(val name: String) {
    companion object {
        @JvmStatic fun of(name: String) = VarId(name)
    }
}

data class FieldRef(val role: RoleId, val param: VarId){
    companion object {
        @JvmStatic fun of(role: RoleId, param: VarId) = FieldRef(role, param)
    }
}
