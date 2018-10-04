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
#include "ActionType.hpp"
#include "CandidateLaneType.hpp"
#include "Vector2i.hpp"

//------------------------------------------------------------------------------
namespace hpc {

/// プレイヤーの行動。
/// @detail 生成された行動は、事前条件(@pre)を満たしている場合にのみ効力を発揮します。
///         それ以外の場合、その行動は無視され、何も起きません。
class Action
{
public:
    /// @name 行動生成
    /// @note プレイヤーはクッキーをとても大切にしているので
    ///       生地を「捨てる」という行動は存在しません。
    //@{
    /// 「指定した生地置き場の生地をオーブンに入れる」という行動を生成する。
    /// @detail aPutPos の位置に生地のカドが来るよう生地は配置されます。
    ///         そこから aPutPos + Vector2i(生地の横幅 - 1, 生地の縦幅 - 1) までを
    ///         対角線とする長方形が、その生地が占有する空間です。
    /// @note 生地を回転させることはできません。
    /// @param aCandidateLaneType 対象の生地置き場。
    /// @param aPieceIndex 生地置き場の何番目の生地を使うか。
    /// @param aPutPos 生地をオーブンのどの位置に置くか。
    /// @pre aPutPos に生地を置いたとき、オーブンの空間に収まっている。
    /// @pre aPutPos に生地を置いたとき、オーブン内の他の生地と重ならない。
    static Action Put(
        CandidateLaneType aCandidateLaneType,
        int aPieceIndex,
        const Vector2i& aPutPos
        );
    /// 「何もしない」という行動を生成する。
    static Action Wait();
    //@}

    /// @name コンストラクタ
    //@{
    /// 「何もしない」という行動を生成するコンストラクタ。
    Action();
    //@}

    /// @name 問い合わせ
    //@{
    /// 行動タイプを取得する。
    ActionType type() const;
    /// 「何もしない」アクションか？
    bool isWaiting() const;
    /// 対象の生地置き場。
    CandidateLaneType candidateLaneType() const;
    /// 生地置き場の何番目の生地を対象とするか。
    int pieceIndex() const;
    /// 生地をオーブンのどの位置に置くか。
    Vector2i putPos() const;
    //@}

private:
    /// @name プライベートメンバ変数
    //@{
    /// この行動の行動タイプ。
    ActionType mType;
    /// 対象の生地置き場。
    CandidateLaneType mCandidateLaneType;
    /// 生地置き場の何番目の生地を対象とするか。
    int mPieceIndex;
    /// 生地をオーブンのどの位置に置くか。
    Vector2i mPutPos;
    //@}
};

} // namespace
// EOF
