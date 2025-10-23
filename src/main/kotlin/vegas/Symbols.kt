package vegas

@JvmInline
value class RoleId(val name: String) {
    override fun toString(): String = name
    companion object {
        @JvmStatic fun of(name: String) = RoleId(name)
    }
}

@JvmInline
value class VarId(val name: String) {
    override fun toString(): String = name
    companion object {
        @JvmStatic fun of(name: String) = VarId(name)
    }
}

data class FieldRef(val role: RoleId, val param: VarId){
    override fun toString(): String = "$role.$param"
    companion object {
        @JvmStatic fun of(role: RoleId, param: VarId) = FieldRef(role, param)
    }
}
