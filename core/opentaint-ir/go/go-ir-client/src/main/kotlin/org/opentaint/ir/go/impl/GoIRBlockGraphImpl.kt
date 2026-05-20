package org.opentaint.ir.go.impl

import org.opentaint.ir.go.api.GoIRBody
import org.opentaint.ir.go.cfg.GoIRBasicBlock
import org.opentaint.ir.go.cfg.GoIRBlockGraph
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.inst.GoIRInstRef
import org.opentaint.ir.go.inst.index

class GoIRBlockGraphImpl(override val body: GoIRBody) : GoIRBlockGraph {
    override val blocks: List<GoIRBasicBlock> get() = body.blocks
    override val entry: GoIRBasicBlock get() = body.entryBlock
    override val recover: GoIRBasicBlock? get() = body.recoverBlock

    // Map from instruction index to block
    private val instToBlock: Map<Int, GoIRBasicBlock> by lazy {
        val map = mutableMapOf<Int, GoIRBasicBlock>()
        for (block in blocks) {
            for (inst in block.instructions) {
                map[inst.index] = block
            }
        }
        map
    }

    override fun blockOf(inst: GoIRInst): GoIRBasicBlock =
        instToBlock[inst.index] ?: throw IllegalArgumentException("Instruction ${inst.index} not found")

    override fun blockOf(ref: GoIRInstRef): GoIRBasicBlock =
        instToBlock[ref.index] ?: throw IllegalArgumentException("Instruction ${ref.index} not found")

    override fun domPreorder(): List<GoIRBasicBlock> {
        // Iterative DFS preorder over the dominator tree.
        // The recursive version overflows the JVM stack on real-world Go
        // projects where some functions produce dominator trees that are
        // effectively linear chains thousands of blocks deep.
        val result = mutableListOf<GoIRBasicBlock>()
        val stack = ArrayDeque<GoIRBasicBlock>()
        stack.addLast(entry)
        while (stack.isNotEmpty()) {
            val block = stack.removeLast()
            result.add(block)
            val children = block.dominatedBlocks
            // Push in reverse so children are visited in original order.
            for (i in children.indices.reversed()) {
                stack.addLast(children[i])
            }
        }
        return result
    }

    override fun domPostorder(): List<GoIRBasicBlock> {
        // Iterative DFS postorder over the dominator tree (same reasoning
        // as domPreorder).
        val result = mutableListOf<GoIRBasicBlock>()
        // Each stack frame is (block, nextChildIndex).
        val blockStack = ArrayDeque<GoIRBasicBlock>()
        val idxStack = ArrayDeque<Int>()
        blockStack.addLast(entry)
        idxStack.addLast(0)
        while (blockStack.isNotEmpty()) {
            val block = blockStack.last()
            val idx = idxStack.last()
            val children = block.dominatedBlocks
            if (idx < children.size) {
                idxStack.removeLast()
                idxStack.addLast(idx + 1)
                blockStack.addLast(children[idx])
                idxStack.addLast(0)
            } else {
                result.add(block)
                blockStack.removeLast()
                idxStack.removeLast()
            }
        }
        return result
    }
}
