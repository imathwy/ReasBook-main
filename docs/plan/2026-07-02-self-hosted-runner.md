# 自建 Linux 服务器 CI 方案实施计划

---

## 一、背景与目标

当前 GitHub Actions 使用 `ubuntu-latest` 托管 runner，每次 run 从空白环境开始，需重新下载并解压约 80 GB 的 mathlib olean cache，导致编译超时（timeout-minutes: 240）。

**目标**：迁移至自有 Linux 服务器作为 self-hosted runner，利用持久化 `.lake/build/` 目录实现增量编译——首次完整编译为一次性成本，后续每次 push 仅重新编译变更文件（预期 5–15 分钟）。

---

## 二、服务器资源要求

| 资源 | 最低配置 | 推荐配置 |
|------|---------|---------|
| CPU | 8 核 | 16 核 |
| RAM | 32 GB | 64 GB |
| 磁盘 | 200 GB SSD | 500 GB SSD |
| 操作系统 | Ubuntu 22.04 LTS | Ubuntu 22.04 LTS |
| 网络 | 100 Mbps | 1 Gbps |

磁盘用量明细：
- mathlib v4.30.0 olean cache：~80 GB（一次性下载，后续不再增长）
- 项目自身编译产物：~2 GB（随项目文件线性增长，每本书约 100–200 MB）
- 源码 + 依赖包（.lake/packages/）：~10 GB
- 余量与多版本并存：~60 GB

---

## 三、服务器初始化

### 3.1 安装基础依赖

```bash
sudo apt-get update
sudo apt-get install -y curl git build-essential
```

### 3.2 安装 elan（Lean 版本管理器）

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source ~/.profile
elan --version
```

### 3.3 设置持久化目录

```bash
# 所有 CI 运行共享同一份编译产物
export PERSIST_ROOT=/data/reasbook-ci
mkdir -p "$PERSIST_ROOT/reasbook_lake"
```

建议将 `PERSIST_ROOT` 设置为 GitHub Actions 仓库变量（`vars.REASBOOK_PERSIST_ROOT`），与 ReasBook 公开仓库保持一致的配置方式。

### 3.4 首次克隆项目并完整编译（一次性）

```bash
git clone https://github.com/optpku/ReasBook-private.git /data/reasbook-src
cd /data/reasbook-src/ReasBook

# 将 .lake 目录软链到持久化路径
rm -rf .lake
ln -sfn "$PERSIST_ROOT/reasbook_lake" .lake

# 解析依赖（克隆所有依赖包）
lake resolve-deps

# 下载 mathlib 预编译 olean（约 80 GB，一次性）
lake exe cache get

# 完整编译（首次约 2–6 小时，取决于 CPU 核数）
lake build
```

首次完整编译完成后，`$PERSIST_ROOT/reasbook_lake/` 中的 oleans 即为后续增量编译的基础。

---

## 四、注册 GitHub Actions Self-Hosted Runner

### 4.1 在 GitHub 仓库注册 runner

进入 `optpku/ReasBook-private` → Settings → Actions → Runners → New self-hosted runner，选择 Linux x64，按页面提示执行：

```bash
# 下载 runner（版本号以页面显示为准）
mkdir /data/actions-runner && cd /data/actions-runner
curl -o actions-runner-linux-x64.tar.gz -L \
  https://github.com/actions/runner/releases/download/v2.x.x/actions-runner-linux-x64-2.x.x.tar.gz
tar xzf actions-runner-linux-x64.tar.gz

# 配置（使用页面提供的 token）
./config.sh --url https://github.com/optpku/ReasBook-private \
            --token <TOKEN> \
            --name reasbook-server \
            --labels self-hosted,Linux,X64 \
            --work /data/actions-runner/_work
```

### 4.2 注册为系统服务（持久运行）

```bash
sudo ./svc.sh install
sudo ./svc.sh start
sudo ./svc.sh status
```

Runner 以系统服务方式运行，服务器重启后自动恢复。

### 4.3 设置仓库变量

在 GitHub 仓库 Settings → Variables → Actions 中添加：

| 变量名 | 值 |
|--------|----|
| `REASBOOK_PERSIST_ROOT` | `/data/reasbook-ci` |

---

## 五、修改 GitHub Actions Workflow

将 `build-core` 和 `build-docs` 的 `runs-on` 从 `ubuntu-latest` 改为 self-hosted runner，并将 `.lake` 目录软链到持久化路径，替换掉现有的 `lean-action` 缓存机制：

```yaml
name: Build and Check Docs

on:
  push:
    branches: [ main ]
  workflow_dispatch:

permissions:
  contents: read

concurrency:
  group: build-${{ github.ref }}
  cancel-in-progress: true

jobs:
  build-core:
    name: Build ReasBook core
    runs-on: [self-hosted, Linux, X64]
    timeout-minutes: 60          # 增量编译预期 5–30 分钟
    env:
      PERSIST_ROOT: ${{ vars.REASBOOK_PERSIST_ROOT }}

    steps:
      - uses: actions/checkout@v4

      - name: Link persistent .lake directory
        run: |
          set -euo pipefail
          persist_root="${PERSIST_ROOT:-/data/reasbook-ci}"
          mkdir -p "$persist_root/reasbook_lake"
          rm -rf ReasBook/.lake
          ln -sfn "$persist_root/reasbook_lake" ReasBook/.lake

      - name: Resolve dependencies
        run: cd ReasBook && lake resolve-deps

      - name: Prime mathlib cache
        run: cd ReasBook && lake exe cache get || true

      - name: Build ReasBook
        run: cd ReasBook && lake build

  build-docs:
    name: Docs (${{ matrix.module }})
    needs: build-core
    runs-on: [self-hosted, Linux, X64]
    timeout-minutes: 30
    env:
      PERSIST_ROOT: ${{ vars.REASBOOK_PERSIST_ROOT }}
    strategy:
      fail-fast: false
      matrix:
        module:
          - Books/AchimKlenkeLean
          - Books/Analysis2_Tao_2022/Book
          # ... （完整列表同当前 build.yml）

    steps:
      - uses: actions/checkout@v4

      - name: Link persistent .lake directory
        run: |
          persist_root="${PERSIST_ROOT:-/data/reasbook-ci}"
          rm -rf ReasBook/.lake
          ln -sfn "$persist_root/reasbook_lake" ReasBook/.lake

      - name: Build docs (${{ matrix.module }})
        run: |
          mod="${{ matrix.module }}"
          mod="${mod//\//.}"
          cd ReasBook
          lake -R -Kenv=dev build "${mod}:docs"
```

关键变化：
- `runs-on: [self-hosted, Linux, X64]`：使用自建服务器
- 软链 `.lake` 到 `PERSIST_ROOT`：复用首次完整编译的产物
- 移除 `lean-action` 的 GitHub cache 步骤（本地磁盘替代）
- `build-core` timeout 从 240 分钟降至 60 分钟（增量编译）

---

## 六、实施顺序

1. **准备服务器**：完成 §3.1–3.3
2. **首次完整编译**：完成 §3.4（可在夜间离线运行，不影响 CI）
3. **注册 runner**：完成 §4.1–4.3
4. **更新 workflow**：按 §5 修改 `build.yml` 并推送
5. **触发一次 CI**：手动 `workflow_dispatch` 验证增量编译是否正常
6. **确认后**：可关闭或删除当前 `ubuntu-latest` 路径的 Actions cache

---

## 七、维护注意事项

- **mathlib 版本升级**时：需在服务器上重新运行 `lake exe cache get`（重新下载对应版本 olean），约 1–2 小时
- **磁盘清理**：如空间紧张，可删除 `$PERSIST_ROOT/reasbook_lake/build/lib/lean/` 下过期的 olean，但会触发一次较长的重新编译
- **并发 CI runs**：`concurrency: cancel-in-progress: true` 已配置，不会出现两个 run 同时写入同一 `.lake` 目录的冲突
- **runner 离线**：若服务器临时不可用，GitHub 会将 job 排队等待，不会 fallback 到 `ubuntu-latest`；如需 fallback，可在 workflow 中配置 `runs-on: [self-hosted, Linux, X64]` 加 `continue-on-error` 并增加一个 fallback job
