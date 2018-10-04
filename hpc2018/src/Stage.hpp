//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once

//------------------------------------------------------------------------------
#include "Action.hpp"
#include "Array.hpp"
#include "CandidateLane.hpp"
#include "Oven.hpp"
#include "Parameter.hpp"
#include "Piece.hpp"
#include "Random.hpp"

//------------------------------------------------------------------------------
namespace hpc {

/// 各生地置き場が使う乱数をまとめたもの
using CandidateLaneRandoms = Array<Random, CandidateLaneType_TERM>;
/// 生地置き場の配列
using CandidateLanes = Array<CandidateLane, CandidateLaneType_TERM>;

/// ステージ。
class Stage
{
public:
    /// @name コンストラクタ
    //@{
    Stage();
    //@}

    /// @name 問い合わせ
    //@{
    /// 現在のターン数。
    int turn() const;
    /// オーブンを取得する。
    const Oven& oven() const;
    /// 生地置き場を取得する。
    /// @param aType 取得したい生地置き場。
    const CandidateLane& candidateLane(CandidateLaneType aType) const;
    //@}

    /// @name 内部用関数
    //@{
    /// 初期化する。
    void init(const RandomSeed& aStageRandomSeed, CandidateLaneRandoms* aLaneRandoms);
    /// 開始フェーズを処理する。
    void processStartPhase();
    /// プレイヤーフェーズを処理する。
    void processPlayerPhase(const Action& aAction);
    /// 終了フェーズを処理する。
    void processEndPhase(CandidateLaneRandoms* aLaneRandoms);
    /// 次のターンへ。
    void advanceTurn();
    /// ステージ終了したか？
    bool isEnd() const;
    //@}

private:
    /// @name 内部実装
    //@{
    /// 全生地置き場を生地で満たす。
    /// @note 生地生成に使う乱数発生器は外部から渡します。
    void fillCandidate(CandidateLaneRandoms* aLaneRandoms);
    /// 指定のターン数分、オーブンの加熱時間を進める。
    void addHeatTurnCount(int aTurnCount);
    /// 現時点で焼き上がっている生地を回収する。
    /// @return 回収された生地の個数。
    int gatherBaked();
    /// プレイヤーフェーズ(Wait)を処理する。
    void processPlayerPhaseWait(const Action& aAction);
    /// プレイヤーフェーズ(Put)を処理する。
    void processPlayerPhasePut(const Action& aAction);
    //@}

    /// @name プライベートメンバ変数
    //@{
    /// 現在のターン数。
    int mTurn;
    /// 現在のスコア。
    int mScore;
    /// オーブン。
    Oven mOven;
    /// 生地置き場。
    CandidateLanes mCandidateLanes;
    //@}
};

} // namespace
// EOF
