import React, { useEffect, useState } from 'react';
import ReactDOM from 'react-dom';
import katex from 'katex';
import { KatexOutput } from '../TeXBlock';
import { ReadOnlyContext, FunctionsContext } from '../contexts';
const inlineEquationRegex = /\$(.*?)\$/g;
import './inline-equation.css';

export const EditEquation = ({ onCancel, onChange, value: initialValue }) => {
	const [value, setValue] = useState(initialValue);
	const [isValid, setIsValid] = useState(false);
	const handleSubmit = () => {
		onChange(value);
	};
	useEffect(() => {
		let invalid = false;
		try {
			katex.__parse(value.substring(1, value.length - 1));
		} catch (e) {
			invalid = true;
		} finally {
			setIsValid(!invalid);
		}
	}, [value]);
	const content = (
		<div className="pe-portal-root">
			<div className="pe-portal-cntn">
				<div className="pe-portal-cntrhlpr">
					<div className="pe-portal-styler">
						<textarea
							className="pe-portal-textarea"
							onFocus={(e) => e.stopPropagation()}
							onBlur={(e) => e.stopPropagation()}
							type="text"
							value={value}
							onChange={(e) => setValue(e.target.value)}
						/>
						{isValid ? (
							<KatexOutput content={value.substring(1, value.length - 1)} />
						) : (
							<div className="pe-portal-error">Invalid Equation</div>
						)}
						<button className="pe-portal-button cancel" onClick={onCancel}>
							Cancel
						</button>
						<button className="pe-portal-button submit" onClick={handleSubmit}>
							Change
						</button>
					</div>
				</div>
			</div>
		</div>
	);
	return content;
};

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
	const [isEditing, setIsEditing] = React.useState(false);
	const isReadOnly = React.useContext(ReadOnlyContext);
	const { openInlineEquationEditor, changeText } = React.useContext(
		FunctionsContext
	);

	const matchResult = new RegExp(inlineEquationRegex).exec(decoratedText);
	const matchedText = matchResult && matchResult[1];
	const katexDisplay = (
		<KatexOutput
			inline
			content={decoratedText.substring(1, decoratedText.length - 1)}
		/>
	);
	return (
		<span style={{ backgroundColor: '', display: 'inline-block' }}>
			{isReadOnly ? (
				katexDisplay
			) : (
				<span
					className={
						'inline-equation-display-wrapper' +
						(isReadOnly ? ' readonly' : ' editable')
					}
				>
					{katexDisplay}
					{isReadOnly ? null : (
						<div className="inline-equation-popover">
							<button
								onClick={(e) => {
									e.stopPropagation();
									e.preventDefault();
									openInlineEquationEditor(blockKey, start, end, decoratedText);
								}}
								className="inline-equation-popover-button"
							>
								Edit
							</button>
							<button
								onClick={(e) => {
									e.stopPropagation();
									e.preventDefault();
									changeText(blockKey, start, end, '');
								}}
								className="inline-equation-popover-button"
							>
								Remove
							</button>
						</div>
					)}
				</span>
			)}
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
