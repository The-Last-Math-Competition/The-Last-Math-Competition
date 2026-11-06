# 9542 最终冻结复核

最终判断：完整阅读全部 Main.lean、独立 verify.py、精确双语原题及既有作者自审后，未发现证明或原题覆盖范围的问题。Main.lean 保持原样，SHA256 为 `99cc222c4cdc897b17225c24ad10ba023828143e7caa9051a7df2152e6eb8752`。

本次实际运行：strict exit 0（29.110 秒），Lake build exit 0（1.562 秒），独立精确有理数验证 exit 0（0.047 秒）。命令、cwd、完整输出分别保存于 `9542-final-status.json` 和 `9542-final-*.log`。strict 实际输出的 11 条公理依赖均恰为 `propext, Classical.choice, Quot.sound`。禁用词扫描为空。构建复用已有依赖和目标；父代理仍将独立 fresh build。

## 对抗性审查结论

1. 熵定义确为 `Re trace (cfc Real.negMulLog A)`。Hermitian 谱定理把它化为真实本征值熵；没有把对角熵或自定义便利泛函冒充 von Neumann 熵。
2. pinching 证明中 `X=VᴴPU, Y=VᴴQU` 的两组单位式给出双随机权；Jensen 的方向正确，特征值非负假设由 PSD 提供。`P+Q=I` 与两个幂等自伴条件足够。
3. 实际信道是三输入、二输出的复线性 Kraus 映射。CP 量化所有有限 ancilla；TP 对任意矩阵成立。Stinespring isometry 以及两个 partial traces 都对任意输入矩阵检查。
4. 互补映射为两块 pinching，保留未选中坐标的 2×2 相干块。不存在以全退相干互补映射偷换信息量的问题。
5. State 恰为全部复 PSD trace-one 矩阵；对角元实且非负的使用正确。共同上界覆盖相干输入。仅在对角输入处使用互补映射固定态，从而得到达到上界的等式。
6. `compoundSingleLetter` 为真实实数 sSup，内部为三信道 finite inf；不允许根据未知信道替换输入态。统一对角态达到 `h(1/3)`；每个单信道分别由 `(1/2,1/4,1/4)` 的置换达到 `log 2`。非空、有限上界和达到性均在 supremum 证明中出现。
7. 严格差距使用精确 `binEntropy_lt_log_two`；独立有理数验证也核对 `log 2-h(1/3)=(1/3)log(32/27)>0`。
8. 原题是三个断言的合取；第一条有限集合容量极小极大等式被反例否定，已经足够否定整体。没有声称另外两个断言被单独否定。

## 公开容量桥接的独立复核

本次亲自重新打开并阅读 https://arxiv.org/pdf/1606.09314 ，版本为 v3（2017-01-25）。PDF 第 4 页 Eq.(2) 定义 purification 互信息；第 5 页 Definition 1 定义同一编码器与解码器适用于整个未知固定无记忆集合的编码模型；第 6 页 Theorem 1 Eq.(7) 给出 `sup_rho inf_s I(rho,N_s)`，适用于平均和最大错误。因而三成员有限集合是该定理的直接实例。

从 purification 表达式到本项目 entropy-exchange 表达式，只使用实际 Stinespring isometry 对纯 purification 产生的三方纯态两侧约化态等谱，所以 entropy exchange 等于互补输出熵。这是数学说明中的标准外部桥接，未作为自定义公理加入 Lean。本项目不声称形式化全部渐近 coding theorem。参考文献用 bits，Lean 用自然对数；将两侧同除正数 `log 2` 后差距不变。

冻结范围：未修改 Main.lean、verify.py、TeX、PDF、共享快照、PR、其他题或编辑器状态。只新增本审查、最终检查脚本和最终原始日志/状态。交由父代理独立审查与发布。
