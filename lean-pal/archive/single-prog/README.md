# 退役した単一Prog構成

2026-09-11に現役の `PalPeg` モジュールから外した記録。ビルド対象ではない。

- `FullMachineProg.lean`：全体を一本のProgへ直列化する条件付きの組み立て。
- `StageLifecycleProg.lean`：そのためのPCテープ・再開点インターフェース。
- `ASSEMBLY_PLAN.md`：一本化を前提としていた旧計画。

最終定理は一本のProgを要求しておらず、有限個の継続は有限制御に保持できる。
現在の方針は [`../../ASSEMBLY_PLAN.md`](../../ASSEMBLY_PLAN.md) を参照。

三つのファイルは退避直前の内容をバイト単位で保存した。未コミットの変更も含む。
元のimportも記録として残しており、このディレクトリでLeanモジュールとして
ビルドするためのものではない。復元する場合はLeanファイルを `PalPeg/` に戻し、
必要なroot importを戻す。旧計画は現行計画を上書きせず参照できる。

退避時のSHA-256:

```text
11fdadfd73e7f212a10b14cf1d498ec7b79c0f2ae5c8f468808e3a8862788990  FullMachineProg.lean
1359cbab4b11c85b74664a205592e981da6dafd8e06d99ab52723c313187c273  StageLifecycleProg.lean
06d90aa5c226b55213825ef34e2c96bfb558b23024192acf80f7cd9e6009663e  ASSEMBLY_PLAN.md
```
