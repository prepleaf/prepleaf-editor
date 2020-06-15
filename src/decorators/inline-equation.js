import React from 'react';
import { KatexOutput } from '../TeXBlock';
const inlineEquationRegex = /\$(.*?)\$/g;

function findWithRegex(regex, contentBlock, callback) {
	const text = contentBlock.getText();
	let matchArr, start;
	while ((matchArr = regex.exec(text)) !== null) {
		start = matchArr.index;
		callback(start, start + matchArr[0].length);
	}
}

const strategy = (contentBlock, callback, contentState) => {
	return findWithRegex(new RegExp(inlineEquationRegex), contentBlock, callback);
};
const InlineEquation = ({
	blockKey,
	contentState,
	decoratedText,
	children,
	start,
	end,
}) => {
	console.log(decoratedText);
	// const block = contentState.getBlockForKey(blockKey);
	// console.log(block.toJS());

	const matchResult = new RegExp(inlineEquationRegex).exec(decoratedText);
	const matchedText = matchResult && matchResult[1];
	return (
		<span style={{ backgroundColor: '', display: 'inline-block' }}>
			<KatexOutput
				inline
				content={decoratedText.substring(1, decoratedText.length - 1)}
			/>
			<span
				style={{
					width: '0',
					height: 0,
					overflow: 'hidden',
					display: 'inline-block',
				}}
			>
				{children}
			</span>
		</span>
	);
};
export default { strategy, component: InlineEquation };
