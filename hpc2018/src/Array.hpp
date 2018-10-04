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
#include <array>
#include "Assert.hpp"

//------------------------------------------------------------------------------
namespace hpc {

/// 最大要素数を指定する可変長配列。
/// @note std::vector と違い、初期化時に std::array で最大数分のメモリを確保するため
///       このクラスから new ,  delete が呼ばれることはありません。
/// @attention TElement にはデストラクタを持つクラスを指定しないでください。
///            デストラクタは正しく呼び出されません。
template <typename TElement, int TCapacity>
class Array
{
public:
    /// @name typedef
    //@{
    typedef std::array<TElement, TCapacity> ArrayType;
    typedef typename ArrayType::iterator iterator;
    typedef typename ArrayType::const_iterator const_iterator;
    //@}

    /// @name コンストラクタ/デストラクタ
    //@{
    /// コンストラクタ。
    /// @note 最大要素数分のデフォルトコンストラクタが呼び出されます。
    ///       POD 型の場合は 0 で埋められます。
    /// @attention 要素数が多い場合はパフォーマンスに注意してください。
    inline Array();
    /// 配列を与えて初期化するコンストラクタ。
    /// @note TElement がデフォルトコンストラクタを持たない場合は
    ///       このコンストラクタを使わなければなりません。
    /// @attention 要素数が多い場合はパフォーマンスに注意してください。
    explicit inline Array(const ArrayType& aArray);
    /// デストラクタ。
    inline ~Array();
    //@}

    /// @name コンテンツ処理
    //@{
    /// 要素を配列の末尾に追加する。
    /// @param aData 追加する要素。
    inline void add(const TElement& aData);
    /// 全ての要素を削除する。
    inline void clear();
    /// 指定位置の要素を削除し、配列を詰める。
    /// @param aIndex 削除する要素の位置。
    inline void erase(int aIndex);
    /// 指定位置に末尾の要素をコピーし、末尾の要素を削除する。
    /// @note オブジェクトの順序が保存されない代わりに、高速に要素を削除できます。
    /// @param aIndex 削除する要素の位置。
    inline void unstableFastErase(int aIndex);
    //@}

    /// @name 要素数
    //@{
    /// 格納されている要素数を取得する。
    /// @note 戻り値の型が size_t ではないため、 size() と区別した名前を付けています。
    inline int count() const;
    /// 格納可能な最大要素数を取得する。
    /// @note static const int でないのは、コンパイラによる挙動の違いを避けるためです。
    inline int maxCount() const;
    /// 配列が空かどうかを取得する。
    inline bool isEmpty() const;
    /// 配列が満杯かどうかを取得する。
    inline bool isFull() const;
    //@}

    /// @name 要素アクセス
    //@{
    /// インデックス指定で要素を取得する。
    /// @note インデックスの範囲チェックを行います。
    /// @param aIndex アクセスしたい要素の位置。
    inline TElement& operator[](const int aIndex);
    /// インデックス指定で要素を取得する。
    /// @note インデックスの範囲チェックを行います。
    /// @param aIndex アクセスしたい要素の位置。
    inline const TElement& operator[](const int aIndex) const;
    //@}

    /// @name イテレータ
    //@{
    /// begin イテレータを取得する。
    inline iterator begin();
    /// end イテレータを取得する。
    inline iterator end();
    /// begin イテレータを取得する。
    inline const_iterator begin() const;
    /// end イテレータを取得する。
    inline const_iterator end() const;
    //@}

private:
    /// @name プライベートメンバ変数
    //@{
    ArrayType mContainer;
    int mCount;
    //@}
};

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
Array<TElement, TCapacity>::Array()
: mContainer()
, mCount(0)
{
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
Array<TElement, TCapacity>::Array(const ArrayType& aArray)
: mContainer(aArray)
, mCount(TCapacity)
{
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
Array<TElement, TCapacity>::~Array()
{
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
void Array<TElement, TCapacity>::add(const TElement& aData)
{
    HPC_ASSERT(!isFull());

    // 追加
    mContainer[mCount] = aData;
    ++mCount;
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
void Array<TElement, TCapacity>::clear()
{
    mCount = 0;
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
void Array<TElement, TCapacity>::erase(int aIndex)
{
    HPC_ASSERT_MIN_TERM_I(aIndex, 0, count());
    for (int i = aIndex; i < count() - 1; ++i) {
        mContainer[i] = mContainer[i + 1];
    }
    --mCount;
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
void Array<TElement, TCapacity>::unstableFastErase(int aIndex)
{
    HPC_ASSERT_MIN_TERM_I(aIndex, 0, count());
    // 指定位置の要素に末尾の要素を上書き
    mContainer[aIndex] = mContainer[count() - 1];
    // 末尾の要素を捨てる
    --mCount;
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
int Array<TElement, TCapacity>::count() const
{
    return mCount;
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
int Array<TElement, TCapacity>::maxCount() const
{
    return TCapacity;
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
bool Array<TElement, TCapacity>::isEmpty() const
{
    return mCount == 0;
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
bool Array<TElement, TCapacity>::isFull() const
{
    return mCount == TCapacity;
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
TElement& Array<TElement, TCapacity>::operator[](const int aIndex)
{
    HPC_ASSERT_MIN_TERM_I(aIndex, 0, mCount);
    return mContainer[aIndex];
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
const TElement& Array<TElement, TCapacity>::operator[](const int aIndex) const
{
    HPC_ASSERT_MIN_TERM_I(aIndex, 0, mCount);
    return mContainer[aIndex];
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
typename Array<TElement, TCapacity>::iterator Array<TElement, TCapacity>::begin()
{
    return mContainer.begin();
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
typename Array<TElement, TCapacity>::iterator Array<TElement, TCapacity>::end()
{
    return mContainer.begin() + mCount;
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
typename Array<TElement, TCapacity>::const_iterator Array<TElement, TCapacity>::begin() const
{
    return mContainer.begin();
}

//------------------------------------------------------------------------------
template <typename TElement, int TCapacity>
typename Array<TElement, TCapacity>::const_iterator Array<TElement, TCapacity>::end() const
{
    return mContainer.begin() + mCount;
}

} // namespace
// EOF
